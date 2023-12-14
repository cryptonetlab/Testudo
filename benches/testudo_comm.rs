use ark_poly_commit::multilinear_pc::MultilinearPC;
use libtestudo::circuit_verifier::TestudoCommVerifier;
use libtestudo::{
  parameters::get_bls12377_fq_params, poseidon_transcript::PoseidonTranscript, sqrt_pst::Polynomial,
};
use ark_std::time::Instant;
use ark_std::marker::PhantomData;
use serde::Serialize;
type F = ark_bls12_377::Fr;
type E = ark_bls12_377::Bls12_377;
use ark_std::UniformRand;
use ark_relations::r1cs::ConstraintSystem;
use ark_ec::bls12::Bls12;
use ark_ec::pairing::Pairing;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_std::rand::SeedableRng;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use rand::rngs::OsRng;
#[derive(Default, Clone, Serialize)]
struct BenchmarkResults {
  power: usize,
  num_constraints: usize,
  proving_time: u128,
}
fn main() {
  let params = get_bls12377_fq_params();

  let mut writer = csv::Writer::from_path("testudo_comm.csv").expect("unable to open csv writer");
  for &s in [5, 10, 15, 20, 25].iter() {
    println!("Running for {} inputs", s);
    let mut rng = ark_std::test_rng();
    let mut br = BenchmarkResults::default();
    br.power = s;
    let num_vars = s;
    let len = 2_usize.pow(num_vars as u32);
    let z: Vec<F> = (0..len).into_iter().map(|_| F::rand(&mut rng)).collect();
    let r: Vec<F> = (0..num_vars)
      .into_iter()
      .map(|_| F::rand(&mut rng))
      .collect();

    let setup_vars = (num_vars as f32 / 2.0).ceil() as usize;
    let gens = MultilinearPC::<E>::setup((num_vars as f32 / 2.0).ceil() as usize, &mut rng);
    let (ck, vk) = MultilinearPC::<E>::trim(&gens, setup_vars);

    let mut pl = Polynomial::from_evaluations(&z.clone());

    let v = pl.eval(&r);

    let (comm_list, t) = pl.commit(&ck);

    let mut prover_transcript = PoseidonTranscript::new(&get_bls12377_fq_params());

    let (u, pst_proof, mipp_proof) = pl.open(&mut prover_transcript, comm_list, &ck, &r, &t);

    let circuit =
      TestudoCommVerifier::<ark_bls12_377::Bls12_377, ark_bls12_377::constraints::PairingVar> {
        params: get_bls12377_fq_params(),
        vk,
        U: u,
        point: r,
        v,
        pst_proof,
        mipp_proof,
        T: t,
        _iv: PhantomData,
      };
    let cs = ConstraintSystem::<<Bls12<ark_bls12_377::Config> as Pairing>::BaseField>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
   // assert!(cs.is_satisfied().unwrap());
    br.num_constraints =  cs.num_constraints();


    let mut rng2 = rand_chacha::ChaChaRng::seed_from_u64(1776);
    let (pk, vk) = Groth16::<ark_bw6_761::BW6_761>::circuit_specific_setup(circuit.clone(), &mut rng2).unwrap();


    let start = Instant::now();

    let proof = Groth16::<ark_bw6_761::BW6_761>::prove(&pk, circuit.clone(), &mut OsRng).unwrap();

    let duration = start.elapsed().as_millis();
    
    br.proving_time = duration;


    let ok = Groth16::<ark_bw6_761::BW6_761>::verify(&pk.vk, &[], &proof).unwrap();
    assert!(ok);

    writer
      .serialize(br)
      .expect("unable to write results to csv");
    writer.flush().expect("wasn't able to flush");
  }
}
