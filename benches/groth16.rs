use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_groth16::prepare_verifying_key;
use ark_groth16::Groth16;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_relations::r1cs::ConstraintSystem;
use ark_std::marker::PhantomData;
use ark_std::time::Instant;
use serde::Serialize;
use std::ops::Mul;
#[derive(Default, Clone, Serialize)]
struct BenchmarkResults {
  power: usize,
  input_constraints: usize,
  g16_proving_time: u128,
}

fn main() {
  let n = 10;
  let nconstraints = (2_usize).pow(n as u32);
  let mut res = BenchmarkResults::default();
  res.power = n;
  res.input_constraints = nconstraints;
  groth16_bench::<ark_bls12_377::Bls12_377>(nconstraints, &mut res);
  let mut writer = csv::Writer::from_path("groth16.csv").expect("unable to open csv writer");
  writer
    .serialize(res)
    .expect("unable to write results to csv");
  writer.flush().expect("wasn't able to flush");
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
