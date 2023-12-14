// use std::time::Instant;

// use ark_poly_commit::multilinear_pc::MultilinearPC;
// use ark_serialize::CanonicalSerialize;
// use libtestudo::{
//   parameters::PoseidonConfiguration, poseidon_transcript::PoseidonTranscript, sqrt_pst::Polynomial,
// };
// use serde::Serialize;
// type F = ark_bls12_377::Fr;
// type E = ark_bls12_377::Bls12_377;
// use ark_std::UniformRand;

// #[derive(Default, Clone, Serialize)]
// struct BenchmarkResults {
//   power: usize,
//   commit_time: u128,
//   opening_time: u128,
//   verification_time: u128,
//   proof_size: usize,
//   commiter_key_size: usize,
// }
// fn main() {
//   let params = ark_bls12_377::Fr::poseidon_params();

//   let mut writer = csv::Writer::from_path("sqrt_pst.csv").expect("unable to open csv writer");
//   for &s in [4, 5, 20, 27].iter() {
//     println!("Running for {} inputs", s);
//     let mut rng = ark_std::test_rng();
//     let mut br = BenchmarkResults::default();
//     br.power = s;
//     let num_vars = s;
//     let len = 2_usize.pow(num_vars as u32);
//     let z: Vec<F> = (0..len).into_iter().map(|_| F::rand(&mut rng)).collect();
//     let r: Vec<F> = (0..num_vars)
//       .into_iter()
//       .map(|_| F::rand(&mut rng))
//       .collect();

//     let setup_vars = (num_vars as f32 / 2.0).ceil() as usize;
//     let gens = MultilinearPC::<E>::setup((num_vars as f32 / 2.0).ceil() as usize, &mut rng);
//     let (ck, vk) = MultilinearPC::<E>::trim(&gens, setup_vars);

//     let mut cks = Vec::<u8>::new();
//     ck.serialize_with_mode(&mut cks, ark_serialize::Compress::Yes)
//       .unwrap();
//     br.commiter_key_size = cks.len();

//     let mut pl = Polynomial::from_evaluations(&z.clone());

//     let v = pl.eval(&r);

//     let start = Instant::now();
//     let (comm_list, t) = pl.commit(&ck);
//     let duration = start.elapsed().as_millis();
//     br.commit_time = duration;

//     let mut prover_transcript = PoseidonTranscript::new(&params);

//     let start = Instant::now();
//     let (u, pst_proof, mipp_proof) = pl.open(&mut prover_transcript, comm_list, &ck, &r, &t);
//     let duration = start.elapsed().as_millis();
//     br.opening_time = duration;

//     let mut p1 = Vec::<u8>::new();
//     let mut p2 = Vec::<u8>::new();
//     pst_proof
//       .serialize_with_mode(&mut p1, ark_serialize::Compress::Yes)
//       .unwrap();

//     mipp_proof
//       .serialize_with_mode(&mut p2, ark_serialize::Compress::Yes)
//       .unwrap();

//     br.proof_size = p1.len() + p2.len();

//     let mut verifier_transcript = PoseidonTranscript::new(&params);

//     let start = Instant::now();
//     let res = Polynomial::verify(
//       &mut verifier_transcript,
//       &vk,
//       &u,
//       &r,
//       v,
//       &pst_proof,
//       &mipp_proof,
//       &t,
//     );
//     let duration = start.elapsed().as_millis();
//     br.verification_time = duration;
//     assert!(res == true);

//     writer
//       .serialize(br)
//       .expect("unable to write results to csv");
//     writer.flush().expect("wasn't able to flush");
//   }
// }
fn main() {}
