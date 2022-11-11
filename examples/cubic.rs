//! Demonstrates how to produces a proof for canonical cubic equation: `x^3 + x + 5 = y`.
//! The example is described in detail [here].
//!
//! The R1CS for this problem consists of the following 4 constraints:
//! `Z0 * Z0 - Z1 = 0`
//! `Z1 * Z0 - Z2 = 0`
//! `(Z2 + Z0) * 1 - Z3 = 0`
//! `(Z3 + 5) * 1 - I0 = 0`
//!
//! [here]: https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649
use ark_std::{One, UniformRand, Zero};
use libspartan::{InputsAssignment, Instance, SNARKGens, VarsAssignment, SNARK};
use merlin::Transcript;

#[allow(non_snake_case)]
fn produce_r1cs() -> (
  usize,
  usize,
  usize,
  usize,
  Instance,
  VarsAssignment,
  InputsAssignment,
) {
  // parameters of the R1CS instance
  let num_cons = 4;
  let num_vars = 4;
  let num_inputs = 1;
  let num_non_zero_entries = 8;

  // We will encode the above constraints into three matrices, where
  // the coefficients in the matrix are in the little-endian byte order
  let mut A: Vec<(usize, usize, Vec<u8>)> = Vec::new();
  let mut B: Vec<(usize, usize, Vec<u8>)> = Vec::new();
  let mut C: Vec<(usize, usize, Vec<u8>)> = Vec::new();

  let one = Scalar::one().into_repr().to_bytes_le();

  // R1CS is a set of three sparse matrices A B C, where is a row for every
  // constraint and a column for every entry in z = (vars, 1, inputs)
  // An R1CS instance is satisfiable iff:
  // Az \circ Bz = Cz, where z = (vars, 1, inputs)

  // constraint 0 entries in (A,B,C)
  // constraint 0 is Z0 * Z0 - Z1 = 0.
  A.push((0, 0, one.clone()));
  B.push((0, 0, one.clone()));
  C.push((0, 1, one.clone()));

  // constraint 1 entries in (A,B,C)
  // constraint 1 is Z1 * Z0 - Z2 = 0.
  A.push((1, 1, one.clone()));
  B.push((1, 0, one.clone()));
  C.push((1, 2, one.clone()));

  // constraint 2 entries in (A,B,C)
  // constraint 2 is (Z2 + Z0) * 1 - Z3 = 0.
  A.push((2, 2, one.clone()));
  A.push((2, 0, one.clone()));
  B.push((2, num_vars, one.clone()));
  C.push((2, 3, one.clone()));

  // constraint 3 entries in (A,B,C)
  // constraint 3 is (Z3 + 5) * 1 - I0 = 0.
  A.push((3, 3, one.clone()));
  A.push((3, num_vars, Scalar::from(5u32).into_repr().to_bytes_le()));
  B.push((3, num_vars, one.clone()));
  C.push((3, num_vars + 1, one.clone()));

  let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();

  // compute a satisfying assignment
  let mut rng = ark_std::rand::thread_rng();
  let z0 = Scalar::rand(&mut rng);
  let z1 = z0 * z0; // constraint 0
  let z2 = z1 * z0; // constraint 1
  let z3 = z2 + z0; // constraint 2
  let i0 = z3 + Scalar::from(5u32); // constraint 3

  // create a VarsAssignment
  let mut vars = vec![Scalar::zero().into_repr().to_bytes_le(); num_vars];
  vars[0] = z0.into_repr().to_bytes_le();
  vars[1] = z1.into_repr().to_bytes_le();
  vars[2] = z2.into_repr().to_bytes_le();
  vars[3] = z3.into_repr().to_bytes_le();
  let assignment_vars = VarsAssignment::new(&vars).unwrap();

  // create an InputsAssignment
  let mut inputs = vec![Scalar::zero().into_repr().to_bytes_le(); num_inputs];
  inputs[0] = i0.into_repr().to_bytes_le();
  let assignment_inputs = InputsAssignment::new(&inputs).unwrap();

  // check if the instance we created is satisfiable
  let res = inst.is_sat(&assignment_vars, &assignment_inputs);
  assert!(res.unwrap(), "should be satisfied");

  (
    num_cons,
    num_vars,
    num_inputs,
    num_non_zero_entries,
    inst,
    assignment_vars,
    assignment_inputs,
  )
}

fn main() {
  // produce an R1CS instance
  let (
    num_cons,
    num_vars,
    num_inputs,
    num_non_zero_entries,
    inst,
    assignment_vars,
    assignment_inputs,
  ) = produce_r1cs();

  // produce public parameters
  let gens = SNARKGens::new(num_cons, num_vars, num_inputs, num_non_zero_entries);

  // create a commitment to the R1CS instance
  let (comm, decomm) = SNARK::encode(&inst, &gens);

  // produce a proof of satisfiability
  let mut prover_transcript = Transcript::new(b"snark_example");
  let proof = SNARK::prove(
    &inst,
    &comm,
    &decomm,
    assignment_vars,
    &assignment_inputs,
    &gens,
    &mut prover_transcript,
  );

  // verify the proof of satisfiability
  let mut verifier_transcript = Transcript::new(b"snark_example");
  assert!(proof
    .verify(&comm, &assignment_inputs, &mut verifier_transcript, &gens)
    .is_ok());
  println!("proof verification successful!");
}
