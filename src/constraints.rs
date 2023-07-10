use ark_ec::pairing::Pairing;
use std::borrow::Borrow;

use crate::{
  math::Math,
  sparse_mlpoly::{SparsePolyEntry, SparsePolynomial},
  unipoly::UniPoly,
};

use ark_ff::PrimeField;

use ark_crypto_primitives::sponge::{
  constraints::CryptographicSpongeVar,
  poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_poly_commit::multilinear_pc::data_structures::Commitment;
use ark_r1cs_std::{
  alloc::{AllocVar, AllocationMode},
  fields::fp::FpVar,
  prelude::{EqGadget, FieldVar},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};

pub struct PoseidonTranscriptVar<F>
where
  F: PrimeField,
{
  pub cs: ConstraintSystemRef<F>,
  pub sponge: PoseidonSpongeVar<F>,
}

impl<F> PoseidonTranscriptVar<F>
where
  F: PrimeField,
{
  pub fn new(cs: ConstraintSystemRef<F>, params: &PoseidonConfig<F>, c_var: FpVar<F>) -> Self {
    let mut sponge = PoseidonSpongeVar::new(cs.clone(), params);

    sponge.absorb(&c_var).unwrap();

    Self { cs, sponge }
  }

  fn append(&mut self, input: &FpVar<F>) -> Result<(), SynthesisError> {
    self.sponge.absorb(&input)
  }

  fn append_vector(&mut self, input_vec: &[FpVar<F>]) -> Result<(), SynthesisError> {
    for input in input_vec.iter() {
      self.append(input)?;
    }
    Ok(())
  }

  fn challenge(&mut self) -> Result<FpVar<F>, SynthesisError> {
    Ok(self.sponge.squeeze_field_elements(1).unwrap().remove(0))
  }

  fn challenge_scalar_vec(&mut self, len: usize) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let c_vars = self.sponge.squeeze_field_elements(len).unwrap();
    Ok(c_vars)
  }
}

/// Univariate polynomial in constraint system
#[derive(Clone)]
pub struct UniPolyVar<F: PrimeField> {
  pub coeffs: Vec<FpVar<F>>,
}

impl<F: PrimeField> AllocVar<UniPoly<F>, F> for UniPolyVar<F> {
  fn new_variable<T: Borrow<UniPoly<F>>>(
    cs: impl Into<Namespace<F>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|c| {
      let cs = cs.into();
      let cp: &UniPoly<F> = c.borrow();
      let mut coeffs_var = Vec::new();
      for coeff in cp.coeffs.iter() {
        let coeff_var = FpVar::<F>::new_variable(cs.clone(), || Ok(coeff), mode)?;
        coeffs_var.push(coeff_var);
      }
      Ok(Self { coeffs: coeffs_var })
    })
  }
}

impl<F: PrimeField> UniPolyVar<F> {
  pub fn eval_at_zero(&self) -> FpVar<F> {
    self.coeffs[0].clone()
  }

  pub fn eval_at_one(&self) -> FpVar<F> {
    let mut res = self.coeffs[0].clone();
    for i in 1..self.coeffs.len() {
      res = &res + &self.coeffs[i];
    }
    res
  }

  // TODO check if mul without reduce can help
  pub fn evaluate(&self, r: &FpVar<F>) -> FpVar<F> {
    let mut eval = self.coeffs[0].clone();
    let mut power = r.clone();

    for i in 1..self.coeffs.len() {
      eval += &power * &self.coeffs[i];
      power *= r;
    }
    eval
  }
}

/// Circuit gadget that implements the sumcheck verifier
#[derive(Clone)]
pub struct SumcheckVerificationCircuit<F: PrimeField> {
  pub polys: Vec<UniPoly<F>>,
}

impl<F: PrimeField> SumcheckVerificationCircuit<F> {
  pub fn verify_sumcheck(
    poly_vars: &[UniPolyVar<F>],
    claim_var: &FpVar<F>,
    transcript_var: &mut PoseidonTranscriptVar<F>,
  ) -> Result<(FpVar<F>, Vec<FpVar<F>>), SynthesisError> {
    let mut e_var = claim_var.clone();
    let mut r_vars: Vec<FpVar<F>> = Vec::new();

    for poly_var in poly_vars.iter() {
      let res = poly_var.eval_at_one() + poly_var.eval_at_zero();
      res.enforce_equal(&e_var)?;
      transcript_var.append_vector(&poly_var.coeffs)?;
      let r_i_var = transcript_var.challenge()?;
      r_vars.push(r_i_var.clone());
      e_var = poly_var.evaluate(&r_i_var.clone());
    }

    Ok((e_var, r_vars))
  }
}

#[derive(Clone)]
pub struct SparsePolyEntryVar<F: PrimeField> {
  idx: usize,
  val_var: FpVar<F>,
}

impl<F: PrimeField> AllocVar<SparsePolyEntry<F>, F> for SparsePolyEntryVar<F> {
  fn new_variable<T: Borrow<SparsePolyEntry<F>>>(
    cs: impl Into<Namespace<F>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    _mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|s| {
      let cs = cs.into();
      let spe: &SparsePolyEntry<F> = s.borrow();
      let val_var = FpVar::<F>::new_witness(cs, || Ok(spe.val))?;
      Ok(Self {
        idx: spe.idx,
        val_var,
      })
    })
  }
}

#[derive(Clone)]
pub struct SparsePolynomialVar<F: PrimeField> {
  Z_var: Vec<SparsePolyEntryVar<F>>,
}

impl<F: PrimeField> AllocVar<SparsePolynomial<F>, F> for SparsePolynomialVar<F> {
  fn new_variable<T: Borrow<SparsePolynomial<F>>>(
    cs: impl Into<Namespace<F>>,
    f: impl FnOnce() -> Result<T, SynthesisError>,
    mode: AllocationMode,
  ) -> Result<Self, SynthesisError> {
    f().and_then(|s| {
      let cs = cs.into();
      let sp: &SparsePolynomial<F> = s.borrow();
      let mut Z_var = Vec::new();
      for spe in sp.Z.iter() {
        let spe_var = SparsePolyEntryVar::new_variable(cs.clone(), || Ok(spe), mode)?;
        Z_var.push(spe_var);
      }
      Ok(Self { Z_var })
    })
  }
}

impl<F: PrimeField> SparsePolynomialVar<F> {
  fn compute_chi(a: &[bool], r_vars: &[FpVar<F>]) -> FpVar<F> {
    let mut chi_i_var = FpVar::<F>::one();
    let one = FpVar::<F>::one();
    for (i, r_var) in r_vars.iter().enumerate() {
      if a[i] {
        chi_i_var *= r_var;
      } else {
        chi_i_var *= &one - r_var;
      }
    }
    chi_i_var
  }

  pub fn evaluate(&self, r_var: &[FpVar<F>]) -> FpVar<F> {
    let mut sum = FpVar::<F>::zero();
    for spe_var in self.Z_var.iter() {
      // potential problem
      let bits = &spe_var.idx.get_bits(r_var.len());
      sum += SparsePolynomialVar::compute_chi(bits, r_var) * &spe_var.val_var;
    }
    sum
  }
}

#[derive(Clone)]
pub struct R1CSVerificationCircuit<F: PrimeField> {
  pub num_vars: usize,
  pub num_cons: usize,
  pub input: Vec<F>,
  pub input_as_sparse_poly: SparsePolynomial<F>,
  pub evals: (F, F, F),
  pub params: PoseidonConfig<F>,
  pub prev_challenge: F,
  pub claims_phase2: (F, F, F, F),
  pub eval_vars_at_ry: F,
  pub sc_phase1: SumcheckVerificationCircuit<F>,
  pub sc_phase2: SumcheckVerificationCircuit<F>,
  // The point on which the polynomial was evaluated by the prover.
  pub claimed_rx: Vec<F>,
  pub claimed_ry: Vec<F>,
  pub claimed_transcript_sat_state: F,
}

impl<F: PrimeField> R1CSVerificationCircuit<F> {
  pub fn new<E: Pairing<ScalarField = F>>(config: &VerifierConfig<E>) -> Self {
    Self {
      num_vars: config.num_vars,
      num_cons: config.num_cons,
      input: config.input.clone(),
      input_as_sparse_poly: config.input_as_sparse_poly.clone(),
      evals: config.evals,
      params: config.params.clone(),
      prev_challenge: config.prev_challenge,
      claims_phase2: config.claims_phase2,
      eval_vars_at_ry: config.eval_vars_at_ry,
      sc_phase1: SumcheckVerificationCircuit {
        polys: config.polys_sc1.clone(),
      },
      sc_phase2: SumcheckVerificationCircuit {
        polys: config.polys_sc2.clone(),
      },
      claimed_rx: config.rx.clone(),
      claimed_ry: config.ry.clone(),
      claimed_transcript_sat_state: config.transcript_sat_state,
    }
  }
}

/// This section implements the sumcheck verification part of Spartan
impl<F: PrimeField> ConstraintSynthesizer<F> for R1CSVerificationCircuit<F> {
  fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
    let initial_challenge_var = FpVar::<F>::new_input(cs.clone(), || Ok(self.prev_challenge))?;
    let mut transcript_var =
      PoseidonTranscriptVar::new(cs.clone(), &self.params, initial_challenge_var);

    let poly_sc1_vars = self
      .sc_phase1
      .polys
      .iter()
      .map(|p| UniPolyVar::new_variable(cs.clone(), || Ok(p), AllocationMode::Witness).unwrap())
      .collect::<Vec<UniPolyVar<_>>>();

    let poly_sc2_vars = self
      .sc_phase2
      .polys
      .iter()
      .map(|p| UniPolyVar::new_variable(cs.clone(), || Ok(p), AllocationMode::Witness).unwrap())
      .collect::<Vec<UniPolyVar<_>>>();

    let input_vars = self
      .input
      .iter()
      .map(|i| FpVar::<F>::new_variable(cs.clone(), || Ok(i), AllocationMode::Input).unwrap())
      .collect::<Vec<FpVar<F>>>();

    let claimed_rx_vars = self
      .claimed_rx
      .iter()
      .map(|r| FpVar::<F>::new_variable(cs.clone(), || Ok(r), AllocationMode::Input).unwrap())
      .collect::<Vec<FpVar<F>>>();

    let claimed_ry_vars = self
      .claimed_ry
      .iter()
      .map(|r| FpVar::<F>::new_variable(cs.clone(), || Ok(r), AllocationMode::Input).unwrap())
      .collect::<Vec<FpVar<F>>>();

    transcript_var.append_vector(&input_vars)?;

    let num_rounds_x = self.num_cons.log_2();
    let _num_rounds_y = (2 * self.num_vars).log_2();

    let tau_vars = transcript_var.challenge_scalar_vec(num_rounds_x)?;

    let claim_phase1_var = FpVar::<F>::new_witness(cs.clone(), || Ok(F::zero()))?;

    let (claim_post_phase1_var, rx_var) = SumcheckVerificationCircuit::<F>::verify_sumcheck(
      &poly_sc1_vars,
      &claim_phase1_var,
      &mut transcript_var,
    )?;

    // The prover sends (rx, ry) to the verifier for the evaluation proof so
    // the constraints need to ensure it is indeed the result from the first
    // round of sumcheck verification.
    for (i, r) in claimed_rx_vars.iter().enumerate() {
      rx_var[i].enforce_equal(r)?;
    }

    let (Az_claim, Bz_claim, Cz_claim, prod_Az_Bz_claims) = &self.claims_phase2;

    let Az_claim_var = FpVar::<F>::new_witness(cs.clone(), || Ok(Az_claim))?;
    let Bz_claim_var = FpVar::<F>::new_witness(cs.clone(), || Ok(Bz_claim))?;
    let Cz_claim_var = FpVar::<F>::new_witness(cs.clone(), || Ok(Cz_claim))?;
    let prod_Az_Bz_claim_var = FpVar::<F>::new_witness(cs.clone(), || Ok(prod_Az_Bz_claims))?;
    let one = FpVar::<F>::one();
    let prod_vars: Vec<FpVar<F>> = (0..rx_var.len())
      .map(|i| (&rx_var[i] * &tau_vars[i]) + (&one - &rx_var[i]) * (&one - &tau_vars[i]))
      .collect();
    let mut taus_bound_rx_var = FpVar::<F>::one();

    for p_var in prod_vars.iter() {
      taus_bound_rx_var *= p_var;
    }

    let expected_claim_post_phase1_var =
      (&prod_Az_Bz_claim_var - &Cz_claim_var) * &taus_bound_rx_var;

    claim_post_phase1_var.enforce_equal(&expected_claim_post_phase1_var)?;

    let r_A_var = transcript_var.challenge()?;
    let r_B_var = transcript_var.challenge()?;
    let r_C_var = transcript_var.challenge()?;

    let claim_phase2_var =
      &r_A_var * &Az_claim_var + &r_B_var * &Bz_claim_var + &r_C_var * &Cz_claim_var;

    let (claim_post_phase2_var, ry_var) = SumcheckVerificationCircuit::<F>::verify_sumcheck(
      &poly_sc2_vars,
      &claim_phase2_var,
      &mut transcript_var,
    )?;

    //  Because the verifier checks the commitment opening on point ry outside
    //  the circuit, the prover needs to send ry to the verifier (making the
    //  proof size O(log n)). As this point is normally obtained by the verifier
    //  from the second round of sumcheck, the circuit needs to ensure the
    //  claimed point, coming from the prover, is actually the point derived
    //  inside the circuit. These additional checks will be removed
    //  when the commitment verification is done inside the circuit.
    //  Moreover, (rx, ry) will be used in the evaluation proof.
    for (i, r) in claimed_ry_vars.iter().enumerate() {
      ry_var[i].enforce_equal(r)?;
    }

    let input_as_sparse_poly_var = SparsePolynomialVar::new_variable(
      cs.clone(),
      || Ok(&self.input_as_sparse_poly),
      AllocationMode::Witness,
    )?;

    let poly_input_eval_var = input_as_sparse_poly_var.evaluate(&ry_var[1..]);

    let eval_vars_at_ry_var = FpVar::<F>::new_input(cs.clone(), || Ok(&self.eval_vars_at_ry))?;

    let eval_Z_at_ry_var =
      (FpVar::<F>::one() - &ry_var[0]) * &eval_vars_at_ry_var + &ry_var[0] * &poly_input_eval_var;

    let (eval_A_r, eval_B_r, eval_C_r) = self.evals;

    let eval_A_r_var = FpVar::<F>::new_input(cs.clone(), || Ok(eval_A_r))?;
    let eval_B_r_var = FpVar::<F>::new_input(cs.clone(), || Ok(eval_B_r))?;
    let eval_C_r_var = FpVar::<F>::new_input(cs.clone(), || Ok(eval_C_r))?;

    let scalar_var = &r_A_var * &eval_A_r_var + &r_B_var * &eval_B_r_var + &r_C_var * &eval_C_r_var;

    let expected_claim_post_phase2_var = eval_Z_at_ry_var * scalar_var;
    claim_post_phase2_var.enforce_equal(&expected_claim_post_phase2_var)?;
    let expected_transcript_state_var = transcript_var.challenge()?;
    let claimed_transcript_state_var =
      FpVar::<F>::new_input(cs, || Ok(self.claimed_transcript_sat_state))?;

    // Ensure that the prover and verifier transcipt views are consistent at
    // the end of the satisfiability proof.
    expected_transcript_state_var.enforce_equal(&claimed_transcript_state_var)?;
    Ok(())
  }
}

#[derive(Clone)]
pub struct VerifierConfig<E: Pairing> {
  pub comm: Commitment<E>,
  pub num_vars: usize,
  pub num_cons: usize,
  pub input: Vec<E::ScalarField>,
  pub input_as_sparse_poly: SparsePolynomial<E::ScalarField>,
  pub evals: (E::ScalarField, E::ScalarField, E::ScalarField),
  pub params: PoseidonConfig<E::ScalarField>,
  pub prev_challenge: E::ScalarField,
  pub claims_phase2: (
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
  ),
  pub eval_vars_at_ry: E::ScalarField,
  pub polys_sc1: Vec<UniPoly<E::ScalarField>>,
  pub polys_sc2: Vec<UniPoly<E::ScalarField>>,
  pub rx: Vec<E::ScalarField>,
  pub ry: Vec<E::ScalarField>,
  pub transcript_sat_state: E::ScalarField,
}

// Skeleton for the polynomial commitment verification circuit
// #[derive(Clone)]
// pub struct VerifierCircuit {
//   pub inner_circuit: R1CSVerificationCircuit,
//   pub inner_proof: GrothProof<I>,
//   pub inner_vk: PreparedVerifyingKey<I>,
//   pub eval_vars_at_ry: Fr,
//   pub claims_phase2: (Fr, Fr, Fr, Fr),
//   pub ry: Vec<Fr>,
//   pub transcript_sat_state: Scalar,
// }

// impl VerifierCircuit {
//   pub fn new<R: Rng + CryptoRng>(
//     config: &VerifierConfig,
//     mut rng: &mut R,
//   ) -> Result<Self, SynthesisError> {
//     let inner_circuit = R1CSVerificationCircuit::new(config);
//     let (pk, vk) = Groth16::<I>::setup(inner_circuit.clone(), &mut rng).unwrap();
//     let proof = Groth16::<I>::prove(&pk, inner_circuit.clone(), &mut rng)?;
//     let pvk = Groth16::<I>::process_vk(&vk).unwrap();
//     Ok(Self {
//       inner_circuit,
//       inner_proof: proof,
//       inner_vk: pvk,
//       eval_vars_at_ry: config.eval_vars_at_ry,
//       claims_phase2: config.claims_phase2,
//       ry: config.ry.clone(),
//       transcript_sat_state: config.transcript_sat_state,
//     })
//   }
// }

// impl ConstraintSynthesizer<Fq> for VerifierCircuit {
//   fn generate_constraints(self, cs: ConstraintSystemRef<Fq>) -> ark_relations::r1cs::Result<()> {
//     let proof_var = ProofVar::<I, IV>::new_witness(cs.clone(), || Ok(self.inner_proof.clone()))?;
//     let (v_A, v_B, v_C, v_AB) = self.claims_phase2;
//     let mut pubs = vec![];
//     pubs.extend(self.ry);
//     pubs.extend(vec![v_A, v_B, v_C, v_AB]);
//     pubs.extend(vec![self.eval_vars_at_ry, self.transcript_sat_state]);
//     let bits = pubs
//       .iter()
//       .map(|c| {
//         let bits: Vec<bool> = BitIteratorLE::new(c.into_bigint().as_ref().to_vec()).collect();
//         Vec::new_witness(cs.clone(), || Ok(bits))
//       })
//       .collect::<Result<Vec<_>, _>>()?;
//     let input_var = BooleanInputVar::<Fr, Fq>::new(bits);
//     let vk_var = PreparedVerifyingKeyVar::new_witness(cs, || Ok(self.inner_vk.clone()))?;
//     Groth16VerifierGadget::verify_with_processed_vk(&vk_var, &input_var, &proof_var)?
//       .enforce_equal(&Boolean::constant(true))?;
//     Ok(())
//   }
// }
