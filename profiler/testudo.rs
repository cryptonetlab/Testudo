// #![allow(non_snake_case)]
// #![allow(clippy::assertions_on_result_states)]

// extern crate libtestudo;
// extern crate merlin;
// use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
// use ark_crypto_primitives::sponge::Absorb;
// use ark_ec::pairing::Pairing;
// use ark_ff::PrimeField;
// use ark_serialize::*;
// use libtestudo::parameters::PoseidonConfiguration;
// use libtestudo::poseidon_transcript::PoseidonTranscript;
// use libtestudo::{
//   testudo_snark::{TestudoSnark, TestudoSnarkGens},
//   Instance,
// };

// fn print(msg: &str) {
//   let star = "* ";
//   println!("{:indent$}{}{}", "", star, msg, indent = 2);
// }

// fn main() {
//   let params = ark_bls12_377::Fr::poseidon_params();
//   profiler::<ark_bls12_377::Bls12_377>(params);
// }

// fn profiler<E>(params: PoseidonConfig<E::ScalarField>)
// where
//   E: Pairing,
//   E::ScalarField: PrimeField,
//   E::ScalarField: Absorb,
// {
//   // the list of number of variables (and constraints) in an R1CS instance
//   let inst_sizes = vec![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

//   println!("Profiler:: SNARK");
//   for &s in inst_sizes.iter() {
//     let num_vars = (2_usize).pow(s as u32);
//     let num_cons = num_vars;
//     let num_inputs = 10;

//     // produce a synthetic R1CSInstance
//     let (inst, vars, inputs) =
//       Instance::<E::ScalarField>::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

//     // produce public generators
//     let gens =
//       TestudoSnarkGens::<E>::setup(num_cons, num_vars, num_inputs, num_cons, params.clone());

//     // create a commitment to R1CSInstance
//     let (comm, decomm) = TestudoSnark::encode(&inst, &gens);

//     // produce a proof of satisfiability
//     let mut prover_transcript = PoseidonTranscript::new(&params.clone());
//     let proof = TestudoSnark::prove(
//       &inst,
//       &comm,
//       &decomm,
//       vars,
//       &inputs,
//       &gens,
//       &mut prover_transcript,
//       params.clone(),
//     )
//     .unwrap();

//     let mut proof_encoded = Vec::new();
//     proof
//       .serialize_with_mode(&mut proof_encoded, Compress::Yes)
//       .unwrap();
//     let msg_proof_len = format!(
//       "TestudoSnark::proof_compressed_len {:?}",
//       proof_encoded.len()
//     );
//     print(&msg_proof_len);

//     // verify the proof of satisfiability
//     let mut verifier_transcript = PoseidonTranscript::new(&params.clone());
//     assert!(proof
//       .verify(
//         &gens,
//         &comm,
//         &inputs,
//         &mut verifier_transcript,
//         params.clone()
//       )
//       .is_ok());

//     println!();
//   }
// }

fn main() {}
