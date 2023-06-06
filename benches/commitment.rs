use std::time::Instant;

use ark_bls12_377::Bls12_377;
use ark_ec::pairing::Pairing;
use ark_poly_commit::multilinear_pc::MultilinearPC;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use libtestudo::{
  parameters::PoseidonConfiguration, poseidon_transcript::PoseidonTranscript, sqrt_pst::Polynomial,
};
use serde::Serialize;

#[derive(Default, Clone, Serialize)]
struct BenchmarkResults {
  power: usize,
  commit_time: u128,
  opening_time: u128,
  verification_time: u128,
  proof_size: usize,
  commiter_key_size: usize,
  pst_commit: u128,
  pst_opening: u128,
  pst_verification: u128,
  pst_proof_size: u128,
}
fn main() {
  testudo_commitment_benchmark::<Bls12_377>("testudo_commitment_bls12377.csv");
  testudo_commitment_benchmark::<ark_blst::Bls12>("testudo_commitment_bls12381.csv");
}

fn testudo_commitment_benchmark<E: Pairing>(fname: &str)
where
  E::ScalarField: PoseidonConfiguration,
{
  let params = E::ScalarField::poseidon_params();
  let mut writer = csv::Writer::from_path(fname).expect("unable to open csv writer");
  for &s in [4, 5, 15, 20, 25].iter() {
    println!("Running for {} inputs", s);
    let mut rng = ark_std::test_rng();
    let mut br = BenchmarkResults::default();
    br.power = s;
    let num_vars = s;
    let len = 2_usize.pow(num_vars as u32);
    bench_pst::<E>(num_vars, &mut br);
    let z: Vec<E::ScalarField> = (0..len)
      .into_iter()
      .map(|_| E::ScalarField::rand(&mut rng))
      .collect();
    let r: Vec<E::ScalarField> = (0..num_vars)
      .into_iter()
      .map(|_| E::ScalarField::rand(&mut rng))
      .collect();

    let setup_vars = (num_vars as f32 / 2.0).ceil() as usize;
    let gens = MultilinearPC::<E>::setup((num_vars as f32 / 2.0).ceil() as usize, &mut rng);
    let (ck, vk) = MultilinearPC::<E>::trim(&gens, setup_vars);

    let mut cks = Vec::<u8>::new();
    ck.serialize_with_mode(&mut cks, ark_serialize::Compress::Yes)
      .unwrap();
    br.commiter_key_size = cks.len();

    let mut pl = Polynomial::from_evaluations(&z.clone());

    let v = pl.eval(&r);

    let start = Instant::now();
    let (comm_list, t) = pl.commit(&ck);
    let duration = start.elapsed().as_millis();
    br.commit_time = duration;

    let mut prover_transcript = PoseidonTranscript::new(&params);

    let start = Instant::now();
    let (u, pst_proof, mipp_proof) = pl.open(&mut prover_transcript, comm_list, &ck, &r, &t);
    let duration = start.elapsed().as_millis();
    br.opening_time = duration;

    let mut p1 = Vec::<u8>::new();
    let mut p2 = Vec::<u8>::new();
    pst_proof
      .serialize_with_mode(&mut p1, ark_serialize::Compress::Yes)
      .unwrap();

    mipp_proof
      .serialize_with_mode(&mut p2, ark_serialize::Compress::Yes)
      .unwrap();

    br.proof_size = p1.len() + p2.len();

    let mut verifier_transcript = PoseidonTranscript::new(&params);

    let start = Instant::now();
    let res = Polynomial::verify(
      &mut verifier_transcript,
      &vk,
      &u,
      &r,
      v,
      &pst_proof,
      &mipp_proof,
      &t,
    );
    let duration = start.elapsed().as_millis();
    br.verification_time = duration;
    assert!(res == true);

    writer
      .serialize(br)
      .expect("unable to write results to csv");
    writer.flush().expect("wasn't able to flush");
  }
}

fn bench_pst<E: Pairing>(num_vars: usize, res: &mut BenchmarkResults) {
  use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
  use ark_poly_commit::multilinear_pc::MultilinearPC;
  let params = MultilinearPC::<E>::setup(num_vars, &mut rand::thread_rng());
  let (comkey, vkey) = MultilinearPC::trim(&params, num_vars);
  let poly = DenseMultilinearExtension::rand(num_vars, &mut rand::thread_rng());

  let start = Instant::now();
  let comm = MultilinearPC::commit(&comkey, &poly);
  res.pst_commit = start.elapsed().as_millis();

  let xs = (0..num_vars)
    .map(|_| E::ScalarField::rand(&mut rand::thread_rng()))
    .collect::<Vec<_>>();
  let y = poly.evaluate(&xs).unwrap();
  let start = Instant::now();
  let proof = MultilinearPC::open(&comkey, &poly, &xs);
  res.pst_opening = start.elapsed().as_millis();

  let start = Instant::now();
  let check = MultilinearPC::check(&vkey, &comm, &xs, y, &proof);
  res.pst_verification = start.elapsed().as_millis();

  let mut b = Vec::new();
  proof.serialize_compressed(&mut b).unwrap();
  res.pst_proof_size = b.len() as u128;

  assert!(check);
}
