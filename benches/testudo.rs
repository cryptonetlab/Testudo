use std::marker::PhantomData;
use std::time::Instant;

use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_groth16::prepare_verifying_key;
use ark_groth16::Groth16;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::AllocVar;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_relations::r1cs::ConstraintSystem;
use ark_serialize::*;
use libtestudo::parameters::PoseidonConfiguration;
use libtestudo::{
  poseidon_transcript::PoseidonTranscript,
  testudo_snark::{TestudoSnark, TestudoSnarkGens},
  Instance,
};
use serde::Serialize;
use std::ops::Mul;

fn main() {
  // bench_with_bls12_377();
  // bench_with_bls12_381();
  bench_with_ark_blst();
}
struct GrothCircuit<F: PrimeField> {
  n_constraints: usize,
  _p: PhantomData<F>,
}

impl<F: PrimeField> GrothCircuit<F> {
  pub fn new(n_constraints: usize) -> Self {
    GrothCircuit {
      n_constraints,
      _p: PhantomData,
    }
  }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for GrothCircuit<F> {
  fn generate_constraints(
    self,
    cs: ark_relations::r1cs::ConstraintSystemRef<F>,
  ) -> ark_relations::r1cs::Result<()> {
    let a = F::rand(&mut rand::thread_rng());
    let mut av = FpVar::new_witness(cs.clone(), || Ok(a))?;
    for _ in 0..self.n_constraints {
      let av = av.clone().mul(av.clone());
    }
    Ok(())
  }
}

#[derive(Default, Clone, Serialize)]
struct BenchmarkResults {
  power: usize,
  input_constraints: usize,
  testudo_proving_time: u128,
  testudo_verification_time: u128,
  sat_proof_size: usize,
  eval_proof_size: usize,
  total_proof_size: usize,
  g16_proving_time: u128,
}

fn bench_with_ark_blst() {
  let params = ark_blst::Scalar::poseidon_params();
  testudo_snark_bench::<ark_blst::Bls12>(params, "testudo_blst", false);
}

fn bench_with_bls12_377() {
  let params = ark_bls12_377::Fr::poseidon_params();
  testudo_snark_bench::<ark_bls12_377::Bls12_377>(params, "testudo_bls12_377", true);
}

fn bench_with_bls12_381() {
  let params = ark_bls12_381::Fr::poseidon_params();
  testudo_snark_bench::<ark_bls12_381::Bls12_381>(params, "testudo_bls12_381", true);
}

fn testudo_snark_bench<E>(params: PoseidonConfig<E::ScalarField>, file_name: &str, verify: bool)
where
  E: Pairing,
  E::ScalarField: PrimeField,
  E::ScalarField: Absorb,
{
  let mut writer = csv::Writer::from_path(file_name).expect("unable to open csv writer");
  for &s in [5, 10, 15, 20, 24].iter() {
    //for &s in [4].iter() {
    println!("Running for {} constraints", s);
    let mut br = BenchmarkResults::default();
    let num_vars = (2_usize).pow(s as u32);
    let num_cons = num_vars;
    br.power = s;
    br.input_constraints = num_cons;
    let num_inputs = 10;

    let (inst, vars, inputs) =
      Instance::<E::ScalarField>::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let mut prover_transcript = PoseidonTranscript::new(&params.clone());

    let gens =
      TestudoSnarkGens::<E>::setup(num_cons, num_vars, num_inputs, num_cons, params.clone());

    let (comm, decomm) = TestudoSnark::<E>::encode(&inst, &gens);

    let start = Instant::now();
    let proof = TestudoSnark::prove(
      &inst,
      &comm,
      &decomm,
      vars,
      &inputs,
      &gens,
      &mut prover_transcript,
      params.clone(),
    )
    .unwrap();
    let duration = start.elapsed().as_millis();
    br.testudo_proving_time = duration;

    let mut sat_proof = Vec::<u8>::new();
    proof
      .r1cs_verifier_proof
      .serialize_with_mode(&mut sat_proof, Compress::Yes)
      .unwrap();
    br.sat_proof_size = sat_proof.len();

    let mut eval_proof = Vec::<u8>::new();
    proof
      .r1cs_eval_proof
      .serialize_with_mode(&mut eval_proof, Compress::Yes)
      .unwrap();
    br.eval_proof_size = eval_proof.len();

    let mut total_proof = Vec::<u8>::new();
    proof
      .serialize_with_mode(&mut total_proof, Compress::Yes)
      .unwrap();
    br.total_proof_size = total_proof.len();

    let mut verifier_transcript = PoseidonTranscript::new(&params.clone());
    let start = Instant::now();

    if verify {
      let res = proof.verify(
        &gens,
        &comm,
        &inputs,
        &mut verifier_transcript,
        params.clone(),
      );
      assert!(res.is_ok());
      let duration = start.elapsed().as_millis();
      br.testudo_verification_time = duration;
    }

    groth16_bench::<E>(num_cons, &mut br);
    writer
      .serialize(br)
      .expect("unable to write results to csv");
    writer.flush().expect("wasn't able to flush");
  }
}

fn groth16_bench<E: Pairing>(n_constraints: usize, res: &mut BenchmarkResults) {
  let params = {
    let c = GrothCircuit::<E::ScalarField>::new(n_constraints);
    Groth16::<E>::generate_random_parameters_with_reduction(c, &mut rand::thread_rng()).unwrap()
  };
  let pvk = prepare_verifying_key(&params.vk);
  println!("Running G16 proving for {} constraints", n_constraints);
  let number_constraints = {
    let circuit = GrothCircuit::<E::ScalarField>::new(n_constraints);
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    cs.num_constraints() as u64
  };
  assert_eq!(number_constraints as usize, n_constraints);
  let start = Instant::now();
  let proof = Groth16::<E>::create_random_proof_with_reduction(
    GrothCircuit::<E::ScalarField>::new(n_constraints),
    &params,
    &mut rand::thread_rng(),
  )
  .expect("proof creation failed");
  let proving_time = start.elapsed().as_millis();
  res.g16_proving_time = proving_time;

  let r = Groth16::<E>::verify_proof(&pvk, &proof, &[]).unwrap();
  assert!(r);
}
