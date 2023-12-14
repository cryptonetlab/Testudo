// use crate::ark_std::One;
// use crate::constraints::R1CSVerificationCircuit;
// use crate::mipp::MippProof;
// use crate::parameters::get_bls12377_fq_params;
// use crate::parameters::params_to_base_field;
// use crate::r1csproof::R1CSGens;
// use crate::r1csproof::R1CSVerifierProof;
// use crate::constraints::VerifierConfig;
// use ark_serialize::CanonicalSerialize;
// use crate::{
//   math::Math,
//   poseidon_transcript::PoseidonTranscript,
//   sparse_mlpoly::{SparsePolyEntry, SparsePolynomial},
//   unipoly::UniPoly,
// };
// use ark_ec::Group;
// use ark_crypto_primitives::snark::SNARKGadget;
// use ark_ec::CurveGroup;
// use ark_ff::Field;
// use ark_groth16::constraints::Groth16VerifierGadget;
// use ark_crypto_primitives::sponge::constraints::AbsorbGadget;
// use ark_crypto_primitives::sponge::{
//   constraints::CryptographicSpongeVar,
//   poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
// };
// use ark_crypto_primitives::Error;
// use ark_ec::pairing::Pairing;
// use ark_ff::BigInteger;
// use ark_ff::PrimeField;
// use ark_groth16::Groth16;
// use ark_groth16::PreparedVerifyingKey;
// use ark_groth16::constraints::PreparedVerifyingKeyVar;
// use ark_poly_commit::multilinear_pc::data_structures::CommitmentG2;
// use ark_poly_commit::multilinear_pc::data_structures::ProofG1;
// use ark_poly_commit::multilinear_pc::{
//   data_structures::{Commitment, CommitterKey, Proof, VerifierKey},
//   MultilinearPC,
// };
// use ark_r1cs_std::groups::bls12::G1Var;
// use ark_r1cs_std::prelude::*;
// use ark_r1cs_std::{
//   alloc::{AllocVar, AllocationMode},
//   fields::fp::FpVar,
//   prelude::{EqGadget, FieldVar},
// };
// use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
// use ark_serialize::Compress;
// use ark_snark::CircuitSpecificSetupSNARK;
// use ark_snark::SNARK;
// use digest::generic_array::typenum::True;
// use rand::CryptoRng;
// use rand::Rng;
// use std::ops::AddAssign;
// use std::ops::Mul;
// use std::ops::MulAssign;
// use std::{borrow::Borrow, marker::PhantomData};
// use ark_groth16;
// type BasePrimeField<E> = <<<E as Pairing>::G1 as CurveGroup>::BaseField as Field>::BasePrimeField;

// pub struct VerifierCircuit<E, IV>
// where
//   E: Pairing,
//   IV: PairingVar<E, BasePrimeField<E>>,
// {
//   // pub inner_circuit: R1CSVerificationCircuit<E::ScalarField>, // circuito Mara

//   // pub inner_proof: ark_groth16::Proof<E>, // PROOF DA VERIFICARE
//   // pub inner_vk: PreparedVerifyingKey<E>,  // GENS.GC.VK

//   pub r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
//   pub input:  Vec<E::ScalarField>,
//   pub evals: (E::ScalarField,E::ScalarField,E::ScalarField),

//   pub transcript: PoseidonTranscript<E::ScalarField>,
//   pub gens: R1CSGens<E>,
//   pub r1cs_proof: R1CSVerifierProof<E>, // SELF
//   pub _iv: PhantomData<IV>,
// }

// impl<E, IV> VerifierCircuit<E, IV>
// where
//   E: Pairing,
//   IV: PairingVar<E, BasePrimeField<E>>,
// {
//   pub fn new(
//     //config: &VerifierConfig<E>,
//     //mut rng: &mut R,
//     r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
//     input: Vec<E::ScalarField>,
//     evals: (E::ScalarField, E::ScalarField, E::ScalarField),
//     transcript: PoseidonTranscript<E::ScalarField>,
//     gens: R1CSGens<E>,
//     r1cs_proof: R1CSVerifierProof<E>,
//   ) -> Result<Self, SynthesisError> {
//     // let inner_circuit =  crate::constraints::R1CSVerificationCircuit::new(config);
//     // let (pk, vk) = Groth16::<E>::setup(inner_circuit.clone(), &mut rng).unwrap();
//     // let proof = Groth16::<E>::prove(&pk, inner_circuit.clone(), &mut rng)?;
//     // let pvk = Groth16::<E>::process_vk(&vk).unwrap();
//     Ok(Self {
//       // inner_circuit,
//       // inner_proof: proof,
//       // inner_vk: pvk,
//       r: r,
//       input: input.to_vec(),
//       evals: evals,
//       transcript: transcript,
//       gens: gens,
//       r1cs_proof,
//       _iv: PhantomData,
//     })
//   }
// }
// impl<E,IV> ConstraintSynthesizer<BasePrimeField<E>> for VerifierCircuit<E,IV>
// where
// E: Pairing,
// IV: PairingVar<E, BasePrimeField<E>>,
// IV::G1Var: CurveVar<E::G1, BasePrimeField<E>>,
// // IV::G2Var: CurveVar<E::G2, E::BaseField>,
// // IV::GTVar: FieldVar<E::TargetField, E::BaseField>,
// {
//   fn generate_constraints(self, cs: ConstraintSystemRef<BasePrimeField<E>>) -> ark_relations::r1cs::Result<()> {

//     // //STEP 1) ALLOCATE INNER_PROOF AS CIRCUIT VARIABLE

//     let (rx, ry) = self.r;
//     let (Ar, Br, Cr) = self.evals;
//     let mut pubs = vec![self.r1cs_proof.initial_state];
//     pubs.extend(self.input.clone());
//     pubs.extend(rx.clone());
//     pubs.extend(ry.clone());
//     pubs.extend(vec![
//       self.r1cs_proof.eval_vars_at_ry,
//       Ar,
//       Br,
//       Cr,
//       self.r1cs_proof.transcript_sat_state,
//     ]);
//     // self.transcript.new_from_state(self.r1cs_proof.transcript_sat_state);

//     let proof_gadget = <Groth16VerifierGadget<E, IV> as SNARKGadget<E::ScalarField,BasePrimeField<E>,Groth16<E>>>::ProofVar::new_witness(cs.clone(), || Ok(self.r1cs_proof.circuit_proof)).unwrap();
//     let vk_gadget = <Groth16VerifierGadget<E, IV> as SNARKGadget<E::ScalarField,BasePrimeField<E>,Groth16<E>>>::VerifyingKeyVar::new_witness(cs.clone(), || Ok(self.gens.gens_gc.vk.clone())).unwrap();

//     let input_gadget= <Groth16VerifierGadget<E, IV> as SNARKGadget<E::ScalarField,BasePrimeField<E>,Groth16<E>>>::InputVar::new_input(cs.clone(), || Ok(pubs)).unwrap();
//     let ver = <Groth16VerifierGadget<E, IV> as SNARKGadget<E::ScalarField,BasePrimeField<E>,Groth16<E>>>::verify(&vk_gadget, &input_gadget, &proof_gadget).unwrap();
//     println!("Verifier groth circuit");
//     ver.enforce_equal(&Boolean::constant(true)).unwrap();

//     // MAPPA DEI PARAMETRI PER CHIAMARE VERIFY
//     //gens.gens_pc.vk = vk
//     // self.comm = r1cs_proof.comm
//     //ry[1..] = point
//     // self.eval_vars_at_ry = v
//     // self.proof_evals_vars_at_ry = pst_proof
//     // self.mipp_proof =mipp_proof
//     // selft.t = T
//     ver_mipp_pst::<E,IV>(cs, self.gens.gens_pc.vk, self.r1cs_proof.comm, ry[1..].to_vec(), self.r1cs_proof.eval_vars_at_ry, self.r1cs_proof.proof_eval_vars_at_ry , self.r1cs_proof.mipp_proof, self.r1cs_proof.t);
//     Ok(())
//   }
// }

// fn ver_mipp_pst<E: Pairing, IV: PairingVar<E, BasePrimeField<E>>>(
//    cs: ConstraintSystemRef<BasePrimeField<E>>,
//    vk: VerifierKey<E>,
//    U: Commitment<E>,
//    point: Vec<E::ScalarField>,
//    v: E::ScalarField,
//    pst_proof: Proof<E>,
//    mipp_proof: MippProof<E>,
//    T: E::TargetField,
// ) -> Result<bool, Error> {

//   // allocate point
//   let mut point_var = Vec::new();
//   for p in point.clone().into_iter() {
//     let scalar_in_fq = &BasePrimeField::<E>::from_bigint(
//       <BasePrimeField<E> as PrimeField>::BigInt::from_bits_le(p.into_bigint().to_bits_le().as_slice()),
//     )
//     .unwrap();
//     let p_var = FpVar::new_input(cs.clone(), || Ok(scalar_in_fq))?;
//     point_var.push(p_var);
//   }
//   let len = point_var.len();
//   let odd = if len % 2 == 1 { 1 } else { 0 };
//   let a_var = &point_var[0..len / 2 + odd];
//   let b_var = &point_var[len / 2 + odd..len];

//   let res_mipp = mipp_verify_gadget_final::<E, IV>(
//     cs.clone(),
//     vk.clone(),
//     &mipp_proof,
//     b_var.to_vec(),
//     U.g_product,
//     &T,
//   );

//   assert!(res_mipp.unwrap() == true);
//   let mut a_rev_var = a_var.to_vec().clone();
//   a_rev_var.reverse();

//   let res_var = check_gadget_final::<E, IV>(
//     cs.clone(),
//     vk,
//     U,
//     &a_rev_var,
//     v,
//     pst_proof,
//   );
//   assert!(res_var.unwrap() == true);

//   Ok(true)
// }

// fn check_gadget_final<E: Pairing, IV: PairingVar<E,BasePrimeField<E>>>(
//   cs: ConstraintSystemRef<BasePrimeField<E>>,
//   vk: VerifierKey<E>,
//   commitment: Commitment<E>,
//   point_var: &Vec<FpVar<BasePrimeField<E>>>,
//   value: E::ScalarField,
//   proof: Proof<E>,
// ) -> Result<bool, Error>
// where
//   IV::G1Var: CurveVar<E::G1, BasePrimeField<E>>,
//   IV::G2Var: CurveVar<E::G2, BasePrimeField<E>>,
//   IV::GTVar: FieldVar<E::TargetField, BasePrimeField<E>>,
// {
//   let vk_g_var = IV::G1Var::new_input(cs.clone(), || Ok(vk.g))?;
//   let vk_h_var = IV::G2Var::new_input(cs.clone(), || Ok(vk.h))?;
//   let mut vk_gmask_var = Vec::new();
//   for g_mask in vk.g_mask_random.clone().into_iter() {
//     let g_mask_var = IV::G1Var::new_input(cs.clone(), || Ok(g_mask))?;
//     vk_gmask_var.push(g_mask_var);
//   }
//   // allocate commitment
//   let com_g1_prod_var = IV::G1Var::new_input(cs.clone(), || Ok(commitment.g_product))?;
//   // allocate value
//   let scalar_in_fq = &BasePrimeField::<E>::from_bigint(
//     <BasePrimeField<E> as PrimeField>::BigInt::from_bits_le(value.into_bigint().to_bits_le().as_slice()),
//   )
//   .unwrap();
//   let value_var = FpVar::new_input(cs.clone(), || Ok(scalar_in_fq))?;
//   // allocate proof
//   let mut proofs_var = Vec::new();
//   for proof in proof.proofs.clone().into_iter() {
//     let proof_var = IV::G2Var::new_witness(cs.clone(), || Ok(proof))?;
//     proofs_var.push(proof_var);
//   }
//   // start operation on circuit
//   let pair_left_op = com_g1_prod_var - (vk_g_var.scalar_mul_le(value_var.to_bits_le()?.iter())?);
//   let left_prepared = IV::prepare_g1(&pair_left_op)?;
//   let right_prepared = IV::prepare_g2(&vk_h_var)?;
//   let left = IV::pairing(left_prepared, right_prepared)?;

//   let mut res_var = Vec::new();

//   for p in point_var.into_iter() {
//     let x = vk_g_var.scalar_mul_le(p.to_bits_le()?.iter())?;
//     res_var.push(x);
//   }

//   //computing other part of the circuit
//   let pairing_lefts_var: Vec<_> = (0..vk.nv)
//             .map(|i| vk_gmask_var[i].clone() - res_var[i].clone()) //.map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
//             .collect();

//   let mut pairing_lefts_prep = Vec::new();
//   for var in pairing_lefts_var.clone().into_iter() {
//     pairing_lefts_prep.push(IV::prepare_g1(&var).unwrap());
//   }

//   let mut pairing_right_prep = Vec::new();
//   for var in proofs_var.clone().into_iter() {
//     pairing_right_prep.push(IV::prepare_g2(&var).unwrap());
//   }

//   let right_ml = IV::miller_loop(&pairing_lefts_prep, &pairing_right_prep)?;
//   let right = IV::final_exponentiation(&right_ml).unwrap();
//   left.enforce_equal(&right); // OK
//   Ok(true)
// }

// fn check_2_gadget_final<E: Pairing, IV: PairingVar<E,BasePrimeField<E>>>(
//   cs: ConstraintSystemRef<BasePrimeField<E>>,
//   vk: VerifierKey<E>,
//   commitment: &CommitmentG2<E>,
//   point_var: &Vec<FpVar<BasePrimeField<E>>>,
//   value_var: FpVar<BasePrimeField<E>>,
//   proof: &ProofG1<E>,
// ) -> Result<bool, Error>
// where
//   IV::G1Var: CurveVar<E::G1, BasePrimeField<E>>,
//   IV::G2Var: CurveVar<E::G2, BasePrimeField<E>>,
//   IV::GTVar: FieldVar<E::TargetField, BasePrimeField<E>>,
// {
//   let vk_g_var = IV::G1Var::new_input(cs.clone(), || Ok(vk.g))?;
//   let vk_h_var = IV::G2Var::new_input(cs.clone(), || Ok(vk.h))?;
//   let mut vk_gmask_var = Vec::new();
//   for g_mask in vk.g_mask_random.clone().into_iter() {
//     let g_mask_var = IV::G1Var::new_input(cs.clone(), || Ok(g_mask))?;
//     vk_gmask_var.push(g_mask_var);
//   }
//   // allocate commitment
//   let com_h_prod_var = IV::G2Var::new_input(cs.clone(), || Ok(commitment.h_product))?;

//   let pair_right_op = com_h_prod_var
//     - (vk_h_var
//       .scalar_mul_le(value_var.to_bits_le().unwrap().iter())
//       .unwrap());
//   let right_prepared = IV::prepare_g2(&pair_right_op)?;
//   let left_prepared = IV::prepare_g1(&vk_g_var)?;
//   let left = IV::pairing(left_prepared, right_prepared)?;

//   let mut h_mul_var = Vec::new();

//   for p in point_var.into_iter() {
//     let x = vk_h_var
//       .scalar_mul_le(p.to_bits_le().unwrap().iter())
//       .unwrap();
//     h_mul_var.push(x);
//   }
//   let h_mask_random = vk.h_mask_random[vk.nv - point_var.len()..].to_vec();
//   let mut h_mask_random_var = Vec::new();
//   for h_mask in h_mask_random.clone().into_iter() {
//     let h_mask_var = IV::G2Var::new_input(cs.clone(), || Ok(h_mask))?;
//     h_mask_random_var.push(h_mask_var);
//   }
//   let pairing_rights_var: Vec<_> = (0..point_var.len())
//         .into_iter()
//         .map(|i| h_mask_random_var[i].clone() - h_mul_var[i].clone()) //.map(|i| vk_gmask_var[i].clone() - g_mul_var[i].clone())
//         .collect();
//   let pairing_rights_var: Vec<IV::G2PreparedVar> = pairing_rights_var
//     .into_iter()
//     .map(|p| IV::prepare_g2(&p).unwrap())
//     .collect();
//   let mut proofs_var = Vec::new();
//   for p in proof.proofs.clone().into_iter() {
//     let proof_var = IV::G1Var::new_input(cs.clone(), || Ok(p))?;
//     proofs_var.push(proof_var);
//   }
//   let pairing_lefts_var: Vec<IV::G1PreparedVar> = proofs_var
//     .into_iter()
//     .map(|p| IV::prepare_g1(&p).unwrap())
//     .collect();

//   let right_ml = IV::miller_loop(&pairing_lefts_var, &pairing_rights_var)?;
//   let right = IV::final_exponentiation(&right_ml)?;

//   left.enforce_equal(&right).unwrap();
//   Ok(true)
// }

// fn mipp_verify_gadget_final<E: Pairing, IV: PairingVar<E,BasePrimeField<E>>>(
//   cs: ConstraintSystemRef<BasePrimeField<E>>,
//   vk: VerifierKey<E>,
//   proof: &MippProof<E>,
//   point_var: Vec<FpVar<BasePrimeField<E>>>,
//   U: E::G1Affine,
//   T: &<E as Pairing>::TargetField,
// ) -> Result<bool, Error>
// where
//   IV::G1Var: CurveVar<E::G1, BasePrimeField<E>>,
//   IV::G2Var: CurveVar<E::G2, BasePrimeField<E>>,
//   IV::GTVar: FieldVar<E::TargetField, BasePrimeField<E>>,
// {
//   let mut comms_u_var = Vec::new();
//   for (first, second) in proof.comms_u.clone().into_iter() {
//     let first_var = IV::G1Var::new_input(cs.clone(), || Ok(first))?;
//     let second_var = IV::G1Var::new_input(cs.clone(), || Ok(second))?;
//     comms_u_var.push((first_var, second_var));
//   }
//   // allocate comms_t
//   let mut comms_t_var = Vec::new();
//   for (first, second) in proof.comms_t.clone().into_iter() {
//     let first_var = IV::GTVar::new_input(cs.clone(), || Ok(first))?;
//     let second_var = IV::GTVar::new_input(cs.clone(), || Ok(second))?;
//     comms_t_var.push((first_var, second_var));
//   }

//   let mut xs = Vec::new();
//   let mut xs_inv = Vec::new();
//   let final_y = BasePrimeField::<E>::one();
//   let mut final_y_var = FpVar::new_input(cs.clone(), || Ok(final_y))?;

//   // start allocate T
//   let T_var = IV::GTVar::new_input(cs.clone(), || Ok(T))?;
//   // start allocate U.g_product
//   let U_g_product_var = IV::G1Var::new_input(cs.clone(), || Ok(U))?;

//   let mut final_res_var: MippTUVar<E, IV> = MippTUVar {
//     tc: T_var.clone(),
//     uc: U_g_product_var.clone(), // Siamo sicuri che possiamo togliere senza problemi il 'into_group'? da testare
//   };

//   // create new transcript inside the circuit instead of taking it from parameters
//   let params: PoseidonConfig<E::BaseField> = params_to_base_field::<E>();
//   let mut transcript_var = PoseidonSpongeVar::new(cs.clone(), &params);

//   // PRIMA ABSORB
//   let mut U_g_product_buf = Vec::new();
//   U_g_product_var
//     .value()
//     .unwrap()
//     .serialize_with_mode(&mut U_g_product_buf, Compress::No)
//     .expect("serialization failed");

//   let mut U_g_product_var_bytes = Vec::new();

//   for b in U_g_product_buf {
//     U_g_product_var_bytes.push(UInt8::new_input(cs.clone(), || Ok(b))?);
//   }

//   transcript_var.absorb(&U_g_product_var_bytes)?;

//   let one_var = FpVar::new_input(cs.clone(), || Ok(BasePrimeField::<E>::one()))?;
//   for (i, (comm_u, comm_t)) in comms_u_var.iter().zip(comms_t_var.iter()).enumerate() {
//     let (comm_u_l, comm_u_r) = comm_u;
//     let (comm_t_l, comm_t_r) = comm_t;
//     // Fiat-Shamir challenge
//     // ABSORB COMM_U_R
//     let mut comm_u_l_buf = Vec::new();
//     comm_u_l
//       .value()
//       .unwrap()
//       .serialize_with_mode(&mut comm_u_l_buf, Compress::No)
//       .expect("serialization failed");

//     let mut comm_u_l_var_bytes = Vec::new();

//     for b in comm_u_l_buf {
//       comm_u_l_var_bytes.push(UInt8::new_input(cs.clone(), || Ok(b))?);
//     }
//     transcript_var.absorb(&comm_u_l_var_bytes)?;
//     // ABSORB COMM_U_R
//     let mut comm_u_r_buf = Vec::new();
//     comm_u_r
//       .value()
//       .unwrap()
//       .serialize_with_mode(&mut comm_u_r_buf, Compress::No)
//       .expect("serialization failed");

//     let mut comm_u_r_var_bytes = Vec::new();

//     for b in comm_u_r_buf {
//       comm_u_r_var_bytes.push(UInt8::new_input(cs.clone(), || Ok(b))?);
//     }
//     transcript_var.absorb(&comm_u_r_var_bytes)?;
//     // ABSORB COMM_T_L
//     let mut comm_t_l_buf = Vec::new();
//     comm_t_l
//       .value()
//       .unwrap()
//       .serialize_with_mode(&mut comm_t_l_buf, Compress::No)
//       .expect("serialization failed");

//     let mut comm_t_l_var_bytes = Vec::new();

//     for b in comm_t_l_buf {
//       comm_t_l_var_bytes.push(UInt8::new_input(cs.clone(), || Ok(b))?);
//     }
//     transcript_var.absorb(&comm_t_l_var_bytes)?;
//     // ABSORB COMM_T_R
//     let mut comm_t_r_buf = Vec::new();
//     comm_t_r
//       .value()
//       .unwrap()
//       .serialize_with_mode(&mut comm_t_r_buf, Compress::No)
//       .expect("serialization failed");

//     let mut comm_t_r_var_bytes = Vec::new();

//     for b in comm_t_r_buf {
//       comm_t_r_var_bytes.push(UInt8::new_input(cs.clone(), || Ok(b))?);
//     }
//     transcript_var.absorb(&comm_t_r_var_bytes)?;

//     let c_inv_var = transcript_var.squeeze_field_elements(1).unwrap().remove(0);
//     let c_var = c_inv_var.inverse().unwrap();

//     xs.push(c_var.clone());
//     xs_inv.push(c_inv_var.clone());

//     final_y_var *= &one_var + c_inv_var.mul(&point_var[i]) - &point_var[i];
//   }

//   enum Op<'a, E: Pairing, IV: PairingVar<E>> {
//     TC(&'a IV::GTVar, FpVar<<E>::BaseField>), // BigInt == FpVar<E::BaseField>
//     UC(&'a IV::G1Var, &'a FpVar<<E>::BaseField>),
//   }

//   let res_var = comms_t_var
//     .iter()
//     .zip(comms_u_var.iter())
//     .zip(xs.iter().zip(xs_inv.iter()))
//     .flat_map(|((comm_t, comm_u), (c, c_inv))| {
//       let (comm_t_l, comm_t_r) = comm_t;
//       let (comm_u_l, comm_u_r) = comm_u;

//       // we multiple left side by x^-1 and right side by x
//       vec![
//         Op::TC(comm_t_l, c_inv.clone()),
//         Op::TC(comm_t_r, c.clone()),
//         Op::UC(comm_u_l, c_inv),
//         Op::UC(comm_u_r, c),
//       ]
//     })
//     .fold(MippTUVar::<E, IV>::default(), |mut res, op: Op<E, IV>| {
//       match op {
//         Op::TC(tx, c) => {
//           // let bits_c = c_var.to_bits_le()?; let exp = t_var.pow_le(&bits_c)?;
//           let tx = tx.pow_le(&c.to_bits_le().unwrap()).unwrap();
//           res.tc.mul_assign(&tx);
//         }
//         Op::UC(zx, c) => {
//           let uxp = zx.scalar_mul_le(c.to_bits_le().unwrap().iter()).unwrap();
//           res.uc.add_assign(&uxp);
//         }
//       }
//       res
//     });

//   let ref_final_res_var = &mut final_res_var;
//   ref_final_res_var.merge(&res_var);

//   let mut rs: FpVar<BasePrimeField<E>> = Vec::new();
//   let m = xs_inv.len();
//   for _i in 0..m {
//     let r = transcript_var.squeeze_field_elements(1).unwrap().remove(0);
//     rs.push(r);
//   }
//   println!("SONO QUA");
//   println!("{}", rs[0].value().unwrap());
//   // let rs_var = rs.clone();
//   let v_var: FpVar<BasePrimeField<E>> = (0..m)
//     .into_iter()
//     .map(|i| &one_var + (&rs[i]).mul(&xs_inv[m - i - 1]) - &rs[i])
//     .fold(one_var.clone(), |acc, x| acc * x); // .product() == fold

//   let comm_h = CommitmentG2::<E> {
//     nv: m,
//     h_product: proof.final_h,
//   };

//   let check_h_var = check_2_gadget_final::<E, IV>(
//     cs.clone(),
//     vk.clone(),
//     &comm_h,
//     &rs,
//     v_var,
//     &proof.pst_proof_h,
//   );
//   let check_h = check_h_var.unwrap();
//   assert!(check_h.clone() == true);
//   let final_a_var = IV::G1Var::new_input(cs.clone(), || Ok(proof.final_a))?;
//   let final_u_var = final_a_var
//     .scalar_mul_le(final_y_var.to_bits_le().unwrap().iter())
//     .unwrap();

//   let final_h_var = IV::G2Var::new_input(cs.clone(), || Ok(proof.final_h))?;

//   let final_u_var_prep = IV::prepare_g1(&final_a_var)?;
//   let final_h_var_prep = IV::prepare_g2(&final_h_var)?;

//   let final_t_var = IV::pairing(final_u_var_prep, final_h_var_prep)?;
//   let check_t = true;

//   //ref_final_res_var.tc.enforce_equal(&final_t_var).unwrap();

//   assert!(check_t == true);

//   let check_u = true;
//   //ref_final_res_var.uc.enforce_equal(&final_u_var).unwrap() {

//   assert!(check_u == true);
//   Ok(check_h & check_u)
// }
