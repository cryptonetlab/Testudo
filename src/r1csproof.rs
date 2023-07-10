#![allow(clippy::too_many_arguments)]
use super::dense_mlpoly::{DensePolynomial, EqPolynomial, PolyCommitmentGens};
use super::errors::ProofVerifyError;
use crate::constraints::{R1CSVerificationCircuit, SumcheckVerificationCircuit, VerifierConfig};
use crate::math::Math;
use crate::mipp::MippProof;
use crate::poseidon_transcript::PoseidonTranscript;
use crate::sqrt_pst::Polynomial;
use crate::sumcheck::SumcheckInstanceProof;
use crate::transcript::Transcript;
use crate::unipoly::UniPoly;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::pairing::Pairing;

use ark_poly_commit::multilinear_pc::data_structures::{Commitment, Proof};
use itertools::Itertools;

use super::r1csinstance::R1CSInstance;

use super::sparse_mlpoly::{SparsePolyEntry, SparsePolynomial};
use super::timer::Timer;
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};

use crate::ark_std::UniformRand;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};

use ark_serialize::*;
use ark_std::{One, Zero};

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct R1CSProof<E: Pairing> {
  // The PST commitment to the multilinear extension of the witness.
  pub comm: Commitment<E>,
  sc_proof_phase1: SumcheckInstanceProof<E::ScalarField>,
  claims_phase2: (
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
    E::ScalarField,
  ),
  sc_proof_phase2: SumcheckInstanceProof<E::ScalarField>,
  pub eval_vars_at_ry: E::ScalarField,
  pub proof_eval_vars_at_ry: Proof<E>,
  rx: Vec<E::ScalarField>,
  ry: Vec<E::ScalarField>,
  // The transcript state after the satisfiability proof was computed.
  pub transcript_sat_state: E::ScalarField,
  pub initial_state: E::ScalarField,
  pub t: E::TargetField,
  pub mipp_proof: MippProof<E>,
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct R1CSVerifierProof<E: Pairing> {
  comm: Commitment<E>,
  circuit_proof: ark_groth16::Proof<E>,
  initial_state: E::ScalarField,
  transcript_sat_state: E::ScalarField,
  eval_vars_at_ry: E::ScalarField,
  proof_eval_vars_at_ry: Proof<E>,
  t: E::TargetField,
  mipp_proof: MippProof<E>,
}

#[derive(Clone)]
pub struct CircuitGens<E: Pairing> {
  pk: ProvingKey<E>,
  vk: VerifyingKey<E>,
}

impl<E> CircuitGens<E>
where
  E: Pairing,
{
  // Performs the circuit-specific setup required by Groth16 for the sumcheck
  // circuit. This is done by filling the struct with dummy elements, ensuring
  // the sizes are correct so the setup matches the circuit that will be proved.
  pub fn setup(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Self {
    let mut rng = rand::thread_rng();

    let uni_polys_round1 = (0..num_cons.log_2())
      .map(|_i| {
        UniPoly::<E::ScalarField>::from_evals(&[
          E::ScalarField::rand(&mut rng),
          E::ScalarField::rand(&mut rng),
          E::ScalarField::rand(&mut rng),
          E::ScalarField::rand(&mut rng),
        ])
      })
      .collect::<Vec<UniPoly<E::ScalarField>>>();

    let uni_polys_round2 = (0..num_vars.log_2() + 1)
      .map(|_i| {
        UniPoly::<E::ScalarField>::from_evals(&[
          E::ScalarField::rand(&mut rng),
          E::ScalarField::rand(&mut rng),
          E::ScalarField::rand(&mut rng),
        ])
      })
      .collect::<Vec<UniPoly<E::ScalarField>>>();

    let circuit = R1CSVerificationCircuit {
      num_vars: num_vars,
      num_cons: num_cons,
      input: (0..num_inputs)
        .map(|_i| E::ScalarField::rand(&mut rng))
        .collect_vec(),
      input_as_sparse_poly: SparsePolynomial::new(
        num_vars.log_2(),
        (0..num_inputs + 1)
          .map(|i| SparsePolyEntry::new(i, E::ScalarField::rand(&mut rng)))
          .collect::<Vec<SparsePolyEntry<E::ScalarField>>>(),
      ),
      evals: (
        E::ScalarField::zero(),
        E::ScalarField::zero(),
        E::ScalarField::zero(),
      ),
      params: poseidon,
      prev_challenge: E::ScalarField::zero(),
      claims_phase2: (
        E::ScalarField::zero(),
        E::ScalarField::zero(),
        E::ScalarField::zero(),
        E::ScalarField::zero(),
      ),
      eval_vars_at_ry: E::ScalarField::zero(),
      sc_phase1: SumcheckVerificationCircuit {
        polys: uni_polys_round1,
      },
      sc_phase2: SumcheckVerificationCircuit {
        polys: uni_polys_round2,
      },
      claimed_rx: (0..num_cons.log_2())
        .map(|_i| E::ScalarField::rand(&mut rng))
        .collect_vec(),
      claimed_ry: (0..num_vars.log_2() + 1)
        .map(|_i| E::ScalarField::rand(&mut rng))
        .collect_vec(),
      claimed_transcript_sat_state: E::ScalarField::zero(),
    };
    let (pk, vk) = Groth16::<E>::setup(circuit.clone(), &mut rng).unwrap();
    CircuitGens { pk, vk }
  }
}

#[derive(Clone)]
pub struct R1CSGens<E: Pairing> {
  gens_pc: PolyCommitmentGens<E>,
  gens_gc: CircuitGens<E>,
}

impl<E: Pairing> R1CSGens<E> {
  // Performs the setup for the polynomial commitment PST and for Groth16.
  pub fn setup(
    label: &'static [u8],
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Self {
    let num_poly_vars = num_vars.log_2();
    let gens_pc = PolyCommitmentGens::setup(num_poly_vars, label);
    let gens_gc = CircuitGens::setup(num_cons, num_vars, num_inputs, poseidon);
    R1CSGens { gens_pc, gens_gc }
  }
}

impl<E> R1CSProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  fn prove_phase_one(
    num_rounds: usize,
    evals_tau: &mut DensePolynomial<E::ScalarField>,
    evals_Az: &mut DensePolynomial<E::ScalarField>,
    evals_Bz: &mut DensePolynomial<E::ScalarField>,
    evals_Cz: &mut DensePolynomial<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (
    SumcheckInstanceProof<E::ScalarField>,
    Vec<E::ScalarField>,
    Vec<E::ScalarField>,
  ) {
    let comb_func =
      |poly_tau_comp: &E::ScalarField,
       poly_A_comp: &E::ScalarField,
       poly_B_comp: &E::ScalarField,
       poly_C_comp: &E::ScalarField|
       -> E::ScalarField { (*poly_tau_comp) * ((*poly_A_comp) * poly_B_comp - poly_C_comp) };

    let (sc_proof_phase_one, r, claims) = SumcheckInstanceProof::prove_cubic_with_additive_term(
      &E::ScalarField::zero(), // claim is zero
      num_rounds,
      evals_tau,
      evals_Az,
      evals_Bz,
      evals_Cz,
      comb_func,
      transcript,
    );

    (sc_proof_phase_one, r, claims)
  }

  fn prove_phase_two(
    num_rounds: usize,
    claim: &E::ScalarField,
    evals_z: &mut DensePolynomial<E::ScalarField>,
    evals_ABC: &mut DensePolynomial<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (
    SumcheckInstanceProof<E::ScalarField>,
    Vec<E::ScalarField>,
    Vec<E::ScalarField>,
  ) {
    let comb_func = |poly_A_comp: &E::ScalarField,
                     poly_B_comp: &E::ScalarField|
     -> E::ScalarField { (*poly_A_comp) * poly_B_comp };
    let (sc_proof_phase_two, r, claims) = SumcheckInstanceProof::prove_quad(
      claim, num_rounds, evals_z, evals_ABC, comb_func, transcript,
    );

    (sc_proof_phase_two, r, claims)
  }

  // Proves the R1CS instance inst is satisfiable given the assignment
  // vars.
  pub fn prove(
    inst: &R1CSInstance<E::ScalarField>,
    vars: Vec<E::ScalarField>,
    input: &[E::ScalarField],
    gens: &R1CSGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (Self, Vec<E::ScalarField>, Vec<E::ScalarField>) {
    let timer_prove = Timer::new("R1CSProof::prove");
    // we currently require the number of |inputs| + 1 to be at most number of vars
    assert!(input.len() < vars.len());

    // create the multilinear witness polynomial from the satisfying assiment
    // expressed as the list of sqrt-sized polynomials
    let mut pl = Polynomial::from_evaluations(&vars.clone());

    let timer_commit = Timer::new("polycommit");

    // commitment list to the satisfying witness polynomial list
    let (comm_list, t) = pl.commit(&gens.gens_pc.ck);

    transcript.append_gt::<E>(b"", &t);

    timer_commit.stop();

    let initial_state = transcript.challenge_scalar(b"");
    transcript.new_from_state(&initial_state);

    transcript.append_scalar_vector(b"", &input);

    let timer_sc_proof_phase1 = Timer::new("prove_sc_phase_one");

    // append input to variables to create a single vector z
    let z = {
      let num_inputs = input.len();
      let num_vars = vars.len();
      let mut z = vars;
      z.extend(&vec![E::ScalarField::one()]); // add constant term in z
      z.extend(input);
      z.extend(&vec![E::ScalarField::zero(); num_vars - num_inputs - 1]); // we will pad with zeros
      z
    };

    // derive the verifier's challenge tau
    let (num_rounds_x, num_rounds_y) = (inst.get_num_cons().log_2(), z.len().log_2());
    let tau = transcript.challenge_scalar_vec(b"", num_rounds_x);
    // compute the initial evaluation table for R(\tau, x)
    let mut poly_tau = DensePolynomial::new(EqPolynomial::new(tau).evals());
    let (mut poly_Az, mut poly_Bz, mut poly_Cz) =
      inst.multiply_vec(inst.get_num_cons(), z.len(), &z);

    let (sc_proof_phase1, rx, _claims_phase1) = R1CSProof::<E>::prove_phase_one(
      num_rounds_x,
      &mut poly_tau,
      &mut poly_Az,
      &mut poly_Bz,
      &mut poly_Cz,
      transcript,
    );
    assert_eq!(poly_tau.len(), 1);
    assert_eq!(poly_Az.len(), 1);
    assert_eq!(poly_Bz.len(), 1);
    assert_eq!(poly_Cz.len(), 1);
    timer_sc_proof_phase1.stop();

    let (tau_claim, Az_claim, Bz_claim, Cz_claim) =
      (&poly_tau[0], &poly_Az[0], &poly_Bz[0], &poly_Cz[0]);
    let prod_Az_Bz_claims = (*Az_claim) * Bz_claim;

    // prove the final step of sum-check #1
    let taus_bound_rx = tau_claim;
    let _claim_post_phase1 = ((*Az_claim) * Bz_claim - Cz_claim) * taus_bound_rx;

    let timer_sc_proof_phase2 = Timer::new("prove_sc_phase_two");
    // combine the three claims into a single claim
    let r_A: E::ScalarField = transcript.challenge_scalar(b"");
    let r_B: E::ScalarField = transcript.challenge_scalar(b"");
    let r_C: E::ScalarField = transcript.challenge_scalar(b"");
    let claim_phase2 = r_A * Az_claim + r_B * Bz_claim + r_C * Cz_claim;

    let evals_ABC = {
      // compute the initial evaluation table for R(\tau, x)
      let evals_rx = EqPolynomial::new(rx.clone()).evals();
      let (evals_A, evals_B, evals_C) =
        inst.compute_eval_table_sparse(inst.get_num_cons(), z.len(), &evals_rx);

      assert_eq!(evals_A.len(), evals_B.len());
      assert_eq!(evals_A.len(), evals_C.len());
      (0..evals_A.len())
        .map(|i| r_A * evals_A[i] + r_B * evals_B[i] + r_C * evals_C[i])
        .collect::<Vec<_>>()
    };

    // another instance of the sum-check protocol
    let (sc_proof_phase2, ry, _claims_phase2) = R1CSProof::<E>::prove_phase_two(
      num_rounds_y,
      &claim_phase2,
      &mut DensePolynomial::new(z),
      &mut DensePolynomial::new(evals_ABC),
      transcript,
    );
    timer_sc_proof_phase2.stop();
    let transcript_sat_state = transcript.challenge_scalar(b"");
    transcript.new_from_state(&transcript_sat_state);

    let timmer_opening = Timer::new("polyopening");

    let (comm, proof_eval_vars_at_ry, mipp_proof) =
      pl.open(transcript, comm_list, &gens.gens_pc.ck, &ry[1..], &t);

    timmer_opening.stop();

    let timer_polyeval = Timer::new("polyeval");
    let eval_vars_at_ry = pl.eval(&ry[1..]);
    timer_polyeval.stop();
    timer_prove.stop();
    (
      R1CSProof {
        comm,
        initial_state,
        sc_proof_phase1,
        claims_phase2: (*Az_claim, *Bz_claim, *Cz_claim, prod_Az_Bz_claims),
        sc_proof_phase2,
        eval_vars_at_ry,
        proof_eval_vars_at_ry,
        rx: rx.clone(),
        ry: ry.clone(),
        transcript_sat_state,
        t,
        mipp_proof,
      },
      rx,
      ry,
    )
  }

  // Creates a Groth16 proof for the verification of sumcheck, expressed
  // as a circuit.
  pub fn prove_verifier(
    &self,
    num_vars: usize,
    num_cons: usize,
    input: &[E::ScalarField],
    evals: &(E::ScalarField, E::ScalarField, E::ScalarField),
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &R1CSGens<E>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<R1CSVerifierProof<E>, ProofVerifyError> {
    // serialise and add the IPP commitment to the transcript
    transcript.append_gt::<E>(b"", &self.t);

    let initial_state = transcript.challenge_scalar(b"");
    transcript.new_from_state(&initial_state);

    let mut input_as_sparse_poly_entries = vec![SparsePolyEntry::new(0, E::ScalarField::one())];
    //remaining inputs
    input_as_sparse_poly_entries.extend(
      (0..input.len())
        .map(|i| SparsePolyEntry::new(i + 1, input[i]))
        .collect::<Vec<SparsePolyEntry<E::ScalarField>>>(),
    );
    let input_as_sparse_poly =
      SparsePolynomial::new(num_vars.log_2() as usize, input_as_sparse_poly_entries);

    let config = VerifierConfig {
      num_vars,
      num_cons,
      input: input.to_vec(),
      evals: *evals,
      params: poseidon,
      prev_challenge: initial_state,
      claims_phase2: self.claims_phase2,
      polys_sc1: self.sc_proof_phase1.polys.clone(),
      polys_sc2: self.sc_proof_phase2.polys.clone(),
      eval_vars_at_ry: self.eval_vars_at_ry,
      input_as_sparse_poly,
      comm: self.comm.clone(),
      rx: self.rx.clone(),
      ry: self.ry.clone(),
      transcript_sat_state: self.transcript_sat_state,
    };

    let circuit = R1CSVerificationCircuit::new(&config);

    let circuit_prover_timer = Timer::new("provecircuit");
    let proof = Groth16::<E>::prove(&gens.gens_gc.pk, circuit, &mut rand::thread_rng()).unwrap();
    circuit_prover_timer.stop();

    Ok(R1CSVerifierProof {
      comm: self.comm.clone(),
      circuit_proof: proof,
      initial_state: self.initial_state,
      transcript_sat_state: self.transcript_sat_state,
      eval_vars_at_ry: self.eval_vars_at_ry,
      proof_eval_vars_at_ry: self.proof_eval_vars_at_ry.clone(),
      t: self.t,
      mipp_proof: self.mipp_proof.clone(),
    })
  }
}

impl<E: Pairing> R1CSVerifierProof<E>
where
  <E as Pairing>::ScalarField: Absorb,
{
  // Verifier the Groth16 proof for the sumcheck circuit and the PST polynomial
  // commitment opening.
  pub fn verify(
    &self,
    r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
    input: &[E::ScalarField],
    evals: &(E::ScalarField, E::ScalarField, E::ScalarField),
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    gens: &R1CSGens<E>,
  ) -> Result<bool, ProofVerifyError> {
    let (rx, ry) = &r;
    let (Ar, Br, Cr) = evals;
    let mut pubs = vec![self.initial_state];
    pubs.extend(input.clone());
    pubs.extend(rx.clone());
    pubs.extend(ry.clone());
    pubs.extend(vec![
      self.eval_vars_at_ry,
      *Ar,
      *Br,
      *Cr,
      self.transcript_sat_state,
    ]);
    transcript.new_from_state(&self.transcript_sat_state);
    par! {
      // verifies the Groth16 proof for the spartan verifier
      let is_verified = Groth16::<E>::verify(&gens.gens_gc.vk, &pubs, &self.circuit_proof).unwrap(),

      // verifies the proof of opening against the result of evaluating the
      // witness polynomial at point ry
        let res = Polynomial::verify(
        transcript,
        &gens.gens_pc.vk,
        &self.comm,
        &ry[1..],
        self.eval_vars_at_ry,
        &self.proof_eval_vars_at_ry,
        &self.mipp_proof,
        &self.t,
      )
    };
    assert!(is_verified == true);
    assert!(res == true);
    Ok(is_verified && res)
  }
}

#[cfg(test)]
mod tests {

  use super::*;

  use ark_ff::PrimeField;
  use ark_std::UniformRand;
  type F = ark_bls12_377::Fr;

  fn produce_tiny_r1cs() -> (R1CSInstance<F>, Vec<F>, Vec<F>) {
    // three constraints over five variables Z1, Z2, Z3, Z4, and Z5
    // rounded to the nearest power of two
    let num_cons = 128;
    let num_vars = 256;
    let num_inputs = 2;

    // encode the above constraints into three matrices
    let mut A: Vec<(usize, usize, F)> = Vec::new();
    let mut B: Vec<(usize, usize, F)> = Vec::new();
    let mut C: Vec<(usize, usize, F)> = Vec::new();

    let one = F::one();
    // constraint 0 entries
    // (Z1 + Z2) * I0 - Z3 = 0;
    A.push((0, 0, one));
    A.push((0, 1, one));
    B.push((0, num_vars + 1, one));
    C.push((0, 2, one));

    // constraint 1 entries
    // (Z1 + I1) * (Z3) - Z4 = 0
    A.push((1, 0, one));
    A.push((1, num_vars + 2, one));
    B.push((1, 2, one));
    C.push((1, 3, one));
    // constraint 3 entries
    // Z5 * 1 - 0 = 0
    A.push((2, 4, one));
    B.push((2, num_vars, one));

    let inst = R1CSInstance::new(num_cons, num_vars, num_inputs, &A, &B, &C);

    // compute a satisfying assignment
    let mut rng = ark_std::rand::thread_rng();
    let i0 = F::rand(&mut rng);
    let i1 = F::rand(&mut rng);
    let z1 = F::rand(&mut rng);
    let z2 = F::rand(&mut rng);
    let z3 = (z1 + z2) * i0; // constraint 1: (Z1 + Z2) * I0 - Z3 = 0;
    let z4 = (z1 + i1) * z3; // constraint 2: (Z1 + I1) * (Z3) - Z4 = 0
    let z5 = F::zero(); //constraint 3

    let mut vars = vec![F::zero(); num_vars];
    vars[0] = z1;
    vars[1] = z2;
    vars[2] = z3;
    vars[3] = z4;
    vars[4] = z5;

    let mut input = vec![F::zero(); num_inputs];
    input[0] = i0;
    input[1] = i1;

    (inst, vars, input)
  }

  #[test]
  fn test_tiny_r1cs() {
    let (inst, vars, input) = tests::produce_tiny_r1cs();
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  #[test]
  fn test_synthetic_r1cs() {
    type F = ark_bls12_377::Fr;
    let (inst, vars, input) = R1CSInstance::<F>::produce_synthetic_r1cs(1024, 1024, 10);
    let is_sat = inst.is_sat(&vars, &input);
    assert!(is_sat);
  }

  use crate::parameters::PoseidonConfiguration;
  #[test]
  fn check_r1cs_proof_ark_blst() {
    let params = ark_blst::Scalar::poseidon_params();
    check_r1cs_proof::<ark_blst::Bls12>(params);
  }
  #[test]
  fn check_r1cs_proof_bls12_377() {
    let params = ark_bls12_377::Fr::poseidon_params();
    check_r1cs_proof::<ark_bls12_377::Bls12_377>(params);
  }

  #[test]
  fn check_r1cs_proof_bls12_381() {
    let params = ark_bls12_381::Fr::poseidon_params();
    check_r1cs_proof::<ark_bls12_381::Bls12_381>(params);
  }
  fn check_r1cs_proof<P>(params: PoseidonConfig<P::ScalarField>)
  where
    P: Pairing,
    P::ScalarField: PrimeField,
    P::ScalarField: Absorb,
  {
    let num_vars = 1024;
    let num_cons = num_vars;
    let num_inputs = 3;
    let (inst, vars, input) =
      R1CSInstance::<P::ScalarField>::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    let gens = R1CSGens::<P>::setup(b"test-m", num_cons, num_vars, num_inputs, params.clone());

    //let params = poseidon_params();
    // let mut random_tape = RandomTape::new(b"proof");

    let mut prover_transcript = PoseidonTranscript::new(&params.clone());
    let c = prover_transcript.challenge_scalar::<P::ScalarField>(b"");
    prover_transcript.new_from_state(&c);
    let (proof, rx, ry) = R1CSProof::prove(&inst, vars, &input, &gens, &mut prover_transcript);

    let inst_evals = inst.evaluate(&rx, &ry);

    prover_transcript.new_from_state(&c);
    let verifier_proof = proof
      .prove_verifier(
        num_vars,
        num_cons,
        &input,
        &inst_evals,
        &mut prover_transcript,
        &gens,
        params.clone(),
      )
      .unwrap();

    let mut verifier_transcript = PoseidonTranscript::new(&params.clone());
    assert!(verifier_proof
      .verify(
        (rx, ry),
        &input,
        &inst_evals,
        &mut verifier_transcript,
        &gens
      )
      .is_ok());
  }
}
