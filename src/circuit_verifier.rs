use crate::ark_std::One;
use crate::mipp::MippProof;
use ark_crypto_primitives::sponge::{
  constraints::CryptographicSpongeVar,
  poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
};
use ark_crypto_primitives::Error;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_poly_commit::multilinear_pc::data_structures::CommitmentG2;
use ark_poly_commit::multilinear_pc::data_structures::ProofG1;
use ark_poly_commit::multilinear_pc::{
  data_structures::{Commitment, Proof, VerifierKey},
};
use ark_r1cs_std::fields::nonnative::NonNativeFieldVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::{
  alloc::AllocVar,
  prelude::{EqGadget, FieldVar},
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_serialize::CanonicalSerialize;
use ark_serialize::Compress;
use std::ops::AddAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::marker::PhantomData;


struct MippTUVar<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  pub tc: IV::GTVar,
  pub uc: IV::G1Var,
}

impl<E, IV> Default for MippTUVar<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  fn default() -> Self {
    Self {
      tc: IV::GTVar::one(),
      uc: IV::G1Var::zero(),
    }
  }
}
impl<E, IV> MippTUVar<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  fn merge(&mut self, other: &Self) {
    self.tc.mul_assign(&other.tc);
    self.uc.add_assign(&other.uc);
  }
}

pub struct TestudoCommVerifier<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
{
  pub params: PoseidonConfig<E::BaseField>,
  pub vk: VerifierKey<E>,
  pub U: Commitment<E>,
  pub point: Vec<E::ScalarField>,
  pub v: E::ScalarField,
  pub pst_proof: Proof<E>,
  pub mipp_proof: MippProof<E>,
  pub T: E::TargetField,
  pub _iv: PhantomData<IV>,
}
impl<E, IV> Clone for TestudoCommVerifier<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
{
  fn clone(&self) -> Self {
    Self {
      params: self.params.clone(),
      vk: self.vk.clone(),
      U: self.U.clone(),
      point: self.point.clone(),
      v: self.v.clone(),
      pst_proof: self.pst_proof.clone(),
      mipp_proof: self.mipp_proof.clone(),
      T: self.T.clone(),
      _iv: self._iv,
    }
  }
}

impl<E, IV> ConstraintSynthesizer<<E as Pairing>::BaseField> for TestudoCommVerifier<E, IV>
where
  E: Pairing,
  IV: PairingVar<E>,
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::G2Var: CurveVar<E::G2, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  fn generate_constraints(
    self,
    cs: ConstraintSystemRef<<E as Pairing>::BaseField>,
  ) -> Result<(), SynthesisError> {


    let mut point_var = Vec::new();
    for p in self.point.clone().into_iter() {
      let p_var =
        NonNativeFieldVar::<E::ScalarField, E::BaseField>::new_witness(cs.clone(), || Ok(p))?;
      point_var.push(p_var);
    }
    let len = point_var.len();
    let odd = if len % 2 == 1 { 1 } else { 0 };
    let a_var = &point_var[0..len / 2 + odd];
    let b_var = &point_var[len / 2 + odd..len];

    mipp_verify_gadget::<E, IV>(
      cs.clone(),
      self.params.clone(),
      self.vk.clone(),
      &self.mipp_proof,
      b_var.to_vec(),
      self.U.g_product,
      &self.T,
    ).unwrap();
    let mut a_rev_var = a_var.to_vec().clone();
    a_rev_var.reverse();

    check_gadget::<E, IV>(
      cs.clone(),
      self.vk,
      self.U,
      &a_rev_var,
      self.v,
      self.pst_proof,
    ).unwrap();
    Ok(())
  }
}

fn check_2_gadget<E: Pairing, IV: PairingVar<E>>(
  cs: ConstraintSystemRef<E::BaseField>,
  vk: VerifierKey<E>,
  commitment: &CommitmentG2<E>,
  point_var: &Vec<NonNativeFieldVar<E::ScalarField, E::BaseField>>,
  value_var: NonNativeFieldVar<E::ScalarField, E::BaseField>,
  proof: &ProofG1<E>,
) -> Result<(), Error>
where
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::G2Var: CurveVar<E::G2, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  let vk_g_var = IV::G1Var::new_witness(cs.clone(), || Ok(vk.g))?;
  let vk_h_var = IV::G2Var::new_witness(cs.clone(), || Ok(vk.h))?;
  let mut vk_gmask_var = Vec::new();
  for g_mask in vk.g_mask_random.clone().into_iter() {
    let g_mask_var = IV::G1Var::new_witness(cs.clone(), || Ok(g_mask))?;
    vk_gmask_var.push(g_mask_var);
  }
  // allocate commitment
  let com_h_prod_var = IV::G2Var::new_witness(cs.clone(), || Ok(commitment.h_product))?;

  let pair_right_op = com_h_prod_var
    - (vk_h_var
      .scalar_mul_le(value_var.to_bits_le().unwrap().iter())
      .unwrap());
  let right_prepared = IV::prepare_g2(&pair_right_op)?;
  let left_prepared = IV::prepare_g1(&vk_g_var)?;
  let left = IV::pairing(left_prepared, right_prepared)?;

  let mut h_mul_var = Vec::new();

  for p in point_var.into_iter() {
    let x = vk_h_var
      .scalar_mul_le(p.to_bits_le().unwrap().iter())
      .unwrap();
    h_mul_var.push(x);
  }
  let h_mask_random = vk.h_mask_random[vk.nv - point_var.len()..].to_vec();
  let mut h_mask_random_var = Vec::new();
  for h_mask in h_mask_random.clone().into_iter() {
    let h_mask_var = IV::G2Var::new_witness(cs.clone(), || Ok(h_mask))?;
    h_mask_random_var.push(h_mask_var);
  }
  let pairing_rights_var: Vec<_> = (0..point_var.len())
        .into_iter()
        .map(|i| h_mask_random_var[i].clone() - h_mul_var[i].clone()) //.map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
        .collect();
  let pairing_rights_var: Vec<IV::G2PreparedVar> = pairing_rights_var
    .into_iter()
    .map(|p| IV::prepare_g2(&p).unwrap())
    .collect();
  let mut proofs_var = Vec::new();
  for p in proof.proofs.clone().into_iter() {
    let proof_var = IV::G1Var::new_witness(cs.clone(), || Ok(p))?;
    proofs_var.push(proof_var);
  }
  let pairing_lefts_var: Vec<IV::G1PreparedVar> = proofs_var
    .into_iter()
    .map(|p| IV::prepare_g1(&p).unwrap())
    .collect();

  let right_ml = IV::miller_loop(&pairing_lefts_var, &pairing_rights_var)?;
  let right = IV::final_exponentiation(&right_ml)?;

  left.enforce_equal(&right).unwrap();
  Ok(())
}

fn check_gadget<E: Pairing, IV: PairingVar<E>>(
  cs: ConstraintSystemRef<E::BaseField>,
  vk: VerifierKey<E>,
  commitment: Commitment<E>,
  point_var: &Vec<NonNativeFieldVar<E::ScalarField, E::BaseField>>,
  value: E::ScalarField,
  proof: Proof<E>,
) -> Result<(), Error>
where
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::G2Var: CurveVar<E::G2, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  let vk_g_var = IV::G1Var::new_witness(cs.clone(), || Ok(vk.g))?;
  let vk_h_var = IV::G2Var::new_witness(cs.clone(), || Ok(vk.h))?;
  let mut vk_gmask_var = Vec::new();
  for g_mask in vk.g_mask_random.clone().into_iter() {
    let g_mask_var = IV::G1Var::new_witness(cs.clone(), || Ok(g_mask))?;
    vk_gmask_var.push(g_mask_var);
  }
  // allocate commitment
  let com_g1_prod_var = IV::G1Var::new_witness(cs.clone(), || Ok(commitment.g_product))?;

  let value_var =
    NonNativeFieldVar::<E::ScalarField, E::BaseField>::new_witness(cs.clone(), || Ok(value))?;

  // allocate proof
  let mut proofs_var = Vec::new();
  for proof in proof.proofs.clone().into_iter() {
    let proof_var = IV::G2Var::new_witness(cs.clone(), || Ok(proof))?;
    proofs_var.push(proof_var);
  }
  // start operation on circuit
  let pair_left_op = com_g1_prod_var - (vk_g_var.scalar_mul_le(value_var.to_bits_le()?.iter())?);
  let left_prepared = IV::prepare_g1(&pair_left_op)?;
  let right_prepared = IV::prepare_g2(&vk_h_var)?;
  let left = IV::pairing(left_prepared, right_prepared)?;

  let mut res_var = Vec::new();

  for p in point_var.into_iter() {
    let x = vk_g_var.scalar_mul_le(p.to_bits_le()?.iter())?;
    res_var.push(x);
  }

  //computing other part of the circuit
  let pairing_lefts_var: Vec<_> = (0..vk.nv)
    .map(|i| vk_gmask_var[i].clone() - res_var[i].clone()) //.map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
    .collect();

  let mut pairing_lefts_prep = Vec::new();
  for var in pairing_lefts_var.clone().into_iter() {
    pairing_lefts_prep.push(IV::prepare_g1(&var).unwrap());
  }

  let mut pairing_right_prep = Vec::new();
  for var in proofs_var.clone().into_iter() {
    pairing_right_prep.push(IV::prepare_g2(&var).unwrap());
  }

  let right_ml = IV::miller_loop(&pairing_lefts_prep, &pairing_right_prep)?;
  let right = IV::final_exponentiation(&right_ml).unwrap();
  left.enforce_equal(&right)?;
  Ok(())
}

fn mipp_verify_gadget<E: Pairing, IV: PairingVar<E>>(
  cs: ConstraintSystemRef<E::BaseField>,
  params: PoseidonConfig<E::BaseField>,
  vk: VerifierKey<E>,
  proof: &MippProof<E>,
  point_var: Vec<NonNativeFieldVar<E::ScalarField, E::BaseField>>,
  U: E::G1Affine,
  T: &<E as Pairing>::TargetField,
) -> Result<(),Error>
where
  IV::G1Var: CurveVar<E::G1, E::BaseField>,
  IV::G2Var: CurveVar<E::G2, E::BaseField>,
  IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
{
  let comms_u = proof.comms_u.clone();
  let comms_t = proof.comms_t.clone();
  let mut comms_u_var = Vec::new();
  for (first, second) in proof.comms_u.clone().into_iter() {
    let first_var = IV::G1Var::new_witness(cs.clone(), || Ok(first))?;
    let second_var = IV::G1Var::new_witness(cs.clone(), || Ok(second))?;
    comms_u_var.push((first_var, second_var));
  }
  // allocate comms_t
  let mut comms_t_var = Vec::new();
  for (first, second) in proof.comms_t.clone().into_iter() {
    let first_var = IV::GTVar::new_witness(cs.clone(), || Ok(first))?;
    let second_var = IV::GTVar::new_witness(cs.clone(), || Ok(second))?;
    comms_t_var.push((first_var, second_var));
  }

  let mut xs = Vec::new();
  let mut xs_inv = Vec::new();

  let final_y = E::ScalarField::one();
  let mut final_y_var =
    NonNativeFieldVar::<E::ScalarField, E::BaseField>::new_witness(cs.clone(), || Ok(final_y))?;

  // start allocate T
  let T_var = IV::GTVar::new_witness(cs.clone(), || Ok(T))?;
  // start allocate U.g_product
  let U_g_product_var = IV::G1Var::new_witness(cs.clone(), || Ok(U))?;

  let mut final_res_var: MippTUVar<E, IV> = MippTUVar {
    tc: T_var.clone(),
    uc: U_g_product_var.clone(),
  };

  // create new transcript inside the circuit instead of taking it from parameters
  let mut transcript_var = PoseidonSpongeVar::new(cs.clone(), &params);

  // FIRST ABSORB
  let mut buf = Vec::new();
  U //take it as naive cause we pass the byte to the hash function
    .serialize_with_mode(&mut buf, Compress::No)
    .expect("serialization failed");

  let mut u_var_vec: Vec<UInt8<_>> = Vec::new();
  for el in buf {
    u_var_vec.push(UInt8::new_witness(cs.clone(), || Ok(el))?);
  }
  transcript_var.absorb(&u_var_vec)?;

  let one_var = NonNativeFieldVar::<E::ScalarField, E::BaseField>::new_witness(cs.clone(), || {
    Ok(E::ScalarField::one())
  })?;

  for (i, (comm_u, comm_t)) in comms_u.iter().zip(comms_t.iter()).enumerate() {
    let (comm_u_l, comm_u_r) = comm_u;
    let (comm_t_l, comm_t_r) = comm_t;
    // Fiat-Shamir challenge
    // ABSORB COMM_U_L
    let mut comm_u_l_buf = Vec::new();
    comm_u_l
      .serialize_with_mode(&mut comm_u_l_buf, Compress::No)
      .expect("serialization failed");

    let mut comm_u_l_var_bytes = Vec::new();

    for b in comm_u_l_buf {
      comm_u_l_var_bytes.push(UInt8::new_witness(cs.clone(), || Ok(b))?);
    }
    transcript_var.absorb(&comm_u_l_var_bytes)?;
    // ABSORB COMM_U_R
    let mut comm_u_r_buf = Vec::new();
    comm_u_r
      .serialize_with_mode(&mut comm_u_r_buf, Compress::No)
      .expect("serialization failed");

    let mut comm_u_r_var_bytes = Vec::new();

    for b in comm_u_r_buf {
      comm_u_r_var_bytes.push(UInt8::new_witness(cs.clone(), || Ok(b))?);
    }
    transcript_var.absorb(&comm_u_r_var_bytes)?;
    // ABSORB COMM_T_L
    let mut comm_t_l_buf = Vec::new();
    comm_t_l
      .serialize_with_mode(&mut comm_t_l_buf, Compress::No)
      .expect("serialization failed");

    let mut comm_t_l_var_bytes = Vec::new();

    for b in comm_t_l_buf {
      comm_t_l_var_bytes.push(UInt8::new_witness(cs.clone(), || Ok(b))?);
    }
    transcript_var.absorb(&comm_t_l_var_bytes)?;
    // ABSORB COMM_T_R
    let mut comm_t_r_buf = Vec::new();
    comm_t_r
      .serialize_with_mode(&mut comm_t_r_buf, Compress::No)
      .expect("serialization failed");

    let mut comm_t_r_var_bytes = Vec::new();

    for b in comm_t_r_buf {
      comm_t_r_var_bytes.push(UInt8::new_witness(cs.clone(), || Ok(b))?);
    }

    transcript_var.absorb(&comm_t_r_var_bytes)?;

    //allocate the digest as circuit variable
    let c_inv_nn = (transcript_var.squeeze_nonnative_field_elements::<E::ScalarField>(1)?).0;
    let c_inv_var = &c_inv_nn[0];

    let c_var = c_inv_var.inverse().unwrap();

    xs.push(c_var.clone());
    xs_inv.push(c_inv_var.clone());

    final_y_var *= &one_var + c_inv_var.mul(&point_var[i]) - &point_var[i];
  }
  enum Op<'a, E: Pairing, IV: PairingVar<E>> {
    TC(
      &'a IV::GTVar,
      NonNativeFieldVar<E::ScalarField, E::BaseField>,
    ),
    UC(
      &'a IV::G1Var,
      &'a NonNativeFieldVar<E::ScalarField, E::BaseField>,
    ),
  }

  let res_var = comms_t_var
    .iter()
    .zip(comms_u_var.iter())
    .zip(xs.iter().zip(xs_inv.iter()))
    .flat_map(|((comm_t, comm_u), (c, c_inv))| {
      let (comm_t_l, comm_t_r) = comm_t;
      let (comm_u_l, comm_u_r) = comm_u;

      // we multiple left side by x^-1 and right side by x
      vec![
        Op::TC(comm_t_l, c_inv.clone()),
        Op::TC(comm_t_r, c.clone()),
        Op::UC(comm_u_l, c_inv),
        Op::UC(comm_u_r, c),
      ]
    })
    .fold(MippTUVar::<E, IV>::default(), |mut res, op: Op<E, IV>| {
      match op {
        Op::TC(tx, c) => {
          let tx = tx.pow_le(&c.to_bits_le().unwrap()).unwrap();
          res.tc.mul_assign(&tx);
        }
        Op::UC(zx, c) => {
          let uxp = zx.scalar_mul_le(c.to_bits_le().unwrap().iter()).unwrap();
          res.uc.add_assign(&uxp);
        }
      }
      res
    });

  let ref_final_res_var = &mut final_res_var;
  ref_final_res_var.merge(&res_var);

  let mut rs = Vec::new();
  let m = xs_inv.len();
  for _i in 0..m {
    let r_nn = (transcript_var.squeeze_nonnative_field_elements::<E::ScalarField>(1)?).0;
    let r = r_nn[0].clone();
    rs.push(r);
  }

  let v_var: NonNativeFieldVar<E::ScalarField, E::BaseField> = (0..m)
    .into_iter()
    .map(|i| &one_var + (&rs[i]).mul(&xs_inv[m - i - 1]) - &rs[i])
    .fold(one_var.clone(), |acc, x| acc * x); // .product() == fold

  let comm_h = CommitmentG2::<E> {
    nv: m,
    h_product: proof.final_h,
  };

    check_2_gadget::<E, IV>(
    cs.clone(),
    vk.clone(),
    &comm_h,
    &rs,
    v_var,
    &proof.pst_proof_h,
  )?;
  let final_a_var = IV::G1Var::new_witness(cs.clone(), || Ok(proof.final_a))?;
  let final_u_var = final_a_var
    .scalar_mul_le(final_y_var.to_bits_le().unwrap().iter())
    .unwrap();

  let final_h_var = IV::G2Var::new_witness(cs.clone(), || Ok(proof.final_h))?;

  let final_u_var_prep = IV::prepare_g1(&final_a_var)?;
  let final_h_var_prep = IV::prepare_g2(&final_h_var)?;

  let final_t_var = IV::pairing(final_u_var_prep, final_h_var_prep)?;

  ref_final_res_var.tc.enforce_equal(&final_t_var).unwrap();

  ref_final_res_var.uc.enforce_equal(&final_u_var).unwrap();

  Ok(())
}
#[cfg(test)]
mod tests {
  use crate::ark_std::UniformRand;
  use ark_bls12_377::Bls12_377;
  use ark_ec::pairing::Pairing;
  use ark_std::vec::Vec;
  type E = Bls12_377;
  use ark_relations::r1cs::ConstraintSystem;
  use super::*;
  use ark_ec::bls12::Bls12;
  type F = ark_bls12_377::Fr;
  use crate::sqrt_pst::Polynomial;
  use ark_poly_commit::multilinear_pc::data_structures::{
    CommitmentG2, CommitterKey, ProofG1, VerifierKey,
  };
  use ark_poly_commit::multilinear_pc::MultilinearPC;
  use crate::parameters::get_bls12377_fq_params;
  use crate::poseidon_transcript::PoseidonTranscript;
  use ark_groth16::Groth16;
  use crate::rand::SeedableRng;
  use ark_crypto_primitives::snark::SNARK;
  use rand::rngs::OsRng;

  #[test]
  fn check_commit() {
    // check odd case
    check_sqrt_poly_commit(6);
  }

  fn check_sqrt_poly_commit(num_vars: u32) {
    let mut rng = ark_std::test_rng();
    let len = 2_usize.pow(num_vars);
    let Z: Vec<F> = (0..len).into_iter().map(|_| F::rand(&mut rng)).collect();
    let r: Vec<F> = (0..num_vars)
      .into_iter()
      .map(|_| F::rand(&mut rng))
      .collect();

    let gens = MultilinearPC::<E>::setup(3, &mut rng);
    let (ck, vk) = MultilinearPC::<E>::trim(&gens, 3);

    let mut pl = Polynomial::from_evaluations(&Z.clone());

    let v = pl.eval(&r);

    let (comm_list, t) = pl.commit(&ck);

    let params = get_bls12377_fq_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);

    let (u, pst_proof, mipp_proof) = pl.open(&mut prover_transcript, comm_list, &ck, &r, &t);

    let mut verifier_transcript = PoseidonTranscript::new(&params);

    // let res = Polynomial::verify(
    //   &mut verifier_transcript,
    //   &vk,
    //   &u,
    //   &r,
    //   v,
    //   &pst_proof,
    //   &mipp_proof,
    //   &t,
    // );
    // assert!(res == true);

    let circuit =
      TestudoCommVerifier::<ark_bls12_377::Bls12_377, ark_bls12_377::constraints::PairingVar> {
        params,
        vk,
        U: u,
        point: r,
        v,
        pst_proof,
        mipp_proof,
        T: t,
        _iv: PhantomData,
      };
    // let cs = ConstraintSystem::<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField>::new_ref();
    // circuit.generate_constraints(cs.clone()).unwrap();
    // println!("Num constraints2: {:?}", cs.num_constraints());
    // assert!(cs.is_satisfied().unwrap());


    let mut rng2 = rand_chacha::ChaChaRng::seed_from_u64(1776);
    let (pk, vk) = Groth16::<ark_bw6_761::BW6_761>::circuit_specific_setup(circuit.clone(), &mut rng2).unwrap();
    let proof = Groth16::<ark_bw6_761::BW6_761>::prove(&pk, circuit.clone(), &mut OsRng).unwrap();
    let ok = Groth16::<ark_bw6_761::BW6_761>::verify(&pk.vk, &[], &proof).unwrap();
    assert!(ok);
  }
}
