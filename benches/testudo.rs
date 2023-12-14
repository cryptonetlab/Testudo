// use std::time::Instant;

// use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
// use ark_crypto_primitives::sponge::Absorb;
// use ark_ec::pairing::Pairing;
// use ark_ff::PrimeField;
// use ark_serialize::*;
// use libtestudo::parameters::PoseidonConfiguration;
// use libtestudo::{
//   poseidon_transcript::PoseidonTranscript,
//   testudo_snark::{TestudoSnark, TestudoSnarkGens},
//   Instance,
// };
// use serde::Serialize;

// #[derive(Default, Clone, Serialize)]
// struct BenchmarkResults {
//   power: usize,
//   input_constraints: usize,
//   testudo_proving_time: u128,
//   testudo_verification_time: u128,
//   sat_proof_size: usize,
//   eval_proof_size: usize,
//   total_proof_size: usize,
// }

// fn main() {
//   bench_with_bls12_377();
//   // bench_with_bls12_381();
//   // bench_with_ark_blst();
// }

// fn bench_with_ark_blst() {
//   let params = ark_blst::Scalar::poseidon_params();
//   testudo_snark_bench::<ark_blst::Bls12>(params, "testudo_blst");
// }

// fn bench_with_bls12_377() {
//   let params = ark_bls12_377::Fr::poseidon_params();
//   testudo_snark_bench::<ark_bls12_377::Bls12_377>(params, "testudo_bls12_377");
// }

// fn bench_with_bls12_381() {
//   let params = ark_bls12_381::Fr::poseidon_params();
//   testudo_snark_bench::<ark_bls12_381::Bls12_381>(params, "testudo_bls12_381");
// }

// fn testudo_snark_bench<E>(params: PoseidonConfig<E::ScalarField>, file_name: &str)
// where
//   E: Pairing,
//   E::ScalarField: PrimeField,
//   E::ScalarField: Absorb,
// {
//   let mut writer = csv::Writer::from_path(file_name).expect("unable to open csv writer");
//   for &s in [4, 5, 10, 12, 14, 16, 18, 20, 22, 24, 26].iter() {
//     println!("Running for {} inputs", s);
//     let mut br = BenchmarkResults::default();
//     let num_vars = (2_usize).pow(s as u32);
//     let num_cons = num_vars;
//     br.power = s;
//     br.input_constraints = num_cons;
//     let num_inputs = 10;

//     let (inst, vars, inputs) =
//       Instance::<E::ScalarField>::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
//     let mut prover_transcript = PoseidonTranscript::new(&params.clone());

//     let gens =
//       TestudoSnarkGens::<E>::setup(num_cons, num_vars, num_inputs, num_cons, params.clone());

//     let (comm, decomm) = TestudoSnark::<E>::encode(&inst, &gens);

//     let start = Instant::now();
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
//     let duration = start.elapsed().as_millis();
//     br.testudo_proving_time = duration;

//     let mut sat_proof = Vec::<u8>::new();
//     proof
//       .r1cs_verifier_proof
//       .serialize_with_mode(&mut sat_proof, Compress::Yes)
//       .unwrap();
//     br.sat_proof_size = sat_proof.len();

//     let mut eval_proof = Vec::<u8>::new();
//     proof
//       .r1cs_eval_proof
//       .serialize_with_mode(&mut eval_proof, Compress::Yes)
//       .unwrap();
//     br.eval_proof_size = eval_proof.len();

//     let mut total_proof = Vec::<u8>::new();
//     proof
//       .serialize_with_mode(&mut total_proof, Compress::Yes)
//       .unwrap();
//     br.total_proof_size = total_proof.len();

//     let mut verifier_transcript = PoseidonTranscript::new(&params.clone());
//     let start = Instant::now();

//     let res = proof.verify(
//       &gens,
//       &comm,
//       &inputs,
//       &mut verifier_transcript,
//       params.clone(),
//     );
//     assert!(res.is_ok());
//     let duration = start.elapsed().as_millis();
//     br.testudo_verification_time = duration;

//     writer
//       .serialize(br)
//       .expect("unable to write results to csv");
//     writer.flush().expect("wasn't able to flush");
//   }
// }

fn main() {}
