#![allow(non_snake_case)]
#![doc = include_str!("../README.md")]
#![allow(clippy::assertions_on_result_states)]

extern crate ark_std;
extern crate core;
extern crate digest;
extern crate lazy_static;
extern crate merlin;
extern crate rand;
extern crate sha3;

#[macro_use]
extern crate json;

#[cfg(feature = "multicore")]
extern crate rayon;

mod commitments;
pub mod dense_mlpoly;
mod errors;
#[macro_use]
pub(crate) mod macros;
mod math;
pub(crate) mod mipp;
mod nizk;
mod product_tree;
pub mod r1csinstance;
pub mod r1csproof;
mod sparse_mlpoly;
pub mod sqrt_pst;
pub mod sumcheck;
pub mod testudo_nizk;
pub mod testudo_snark;
mod timer;
pub mod transcript;
mod unipoly;

pub mod parameters;

pub mod constraints;
pub mod poseidon_transcript;

use core::cmp::max;
use errors::R1CSError;

use r1csinstance::{R1CSCommitment, R1CSDecommitment, R1CSInstance};

use ark_ec::CurveGroup;

/// `ComputationCommitment` holds a public preprocessed NP statement (e.g., R1CS)
pub struct ComputationCommitment<G: CurveGroup> {
  comm: R1CSCommitment<G>,
}

use ark_ff::PrimeField;
/// `ComputationDecommitment` holds information to decommit `ComputationCommitment`
pub struct ComputationDecommitment<F: PrimeField> {
  decomm: R1CSDecommitment<F>,
}

/// `Assignment` holds an assignment of values to either the inputs or variables in an `Instance`
#[derive(Clone)]
pub struct Assignment<F: PrimeField> {
  assignment: Vec<F>,
}

impl<F: PrimeField> Assignment<F> {
  /// Constructs a new `Assignment` from a vector
  pub fn new(assignment: &Vec<Vec<u8>>) -> Result<Self, R1CSError> {
    let bytes_to_scalar = |vec: &Vec<Vec<u8>>| -> Result<Vec<F>, R1CSError> {
      let mut vec_scalar: Vec<F> = Vec::new();
      for v in vec {
        let val = F::from_random_bytes(v.as_slice());
        if let Some(v) = val {
          vec_scalar.push(v);
        } else {
          return Err(R1CSError::InvalidScalar);
        }
      }
      Ok(vec_scalar)
    };

    let assignment_scalar = bytes_to_scalar(assignment);

    // check for any parsing errors
    if assignment_scalar.is_err() {
      return Err(R1CSError::InvalidScalar);
    }

    Ok(Assignment {
      assignment: assignment_scalar.unwrap(),
    })
  }

  /// pads Assignment to the specified length
  fn pad(&self, len: usize) -> VarsAssignment<F> {
    // check that the new length is higher than current length
    assert!(len > self.assignment.len());

    let padded_assignment = {
      let mut padded_assignment = self.assignment.clone();
      padded_assignment.extend(vec![F::zero(); len - self.assignment.len()]);
      padded_assignment
    };

    VarsAssignment {
      assignment: padded_assignment,
    }
  }
}

/// `VarsAssignment` holds an assignment of values to variables in an `Instance`
pub type VarsAssignment<F> = Assignment<F>;

/// `InputsAssignment` holds an assignment of values to variables in an `Instance`
pub type InputsAssignment<F> = Assignment<F>;

/// `Instance` holds the description of R1CS matrices and a hash of the matrices
pub struct Instance<F: PrimeField> {
  inst: R1CSInstance<F>,
  digest: Vec<u8>,
}

impl<F: PrimeField> Instance<F> {
  /// Constructs a new `Instance` and an associated satisfying assignment
  pub fn new(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    A: &[(usize, usize, Vec<u8>)],
    B: &[(usize, usize, Vec<u8>)],
    C: &[(usize, usize, Vec<u8>)],
  ) -> Result<Self, R1CSError> {
    let (num_vars_padded, num_cons_padded) = {
      let num_vars_padded = {
        let mut num_vars_padded = num_vars;

        // ensure that num_inputs + 1 <= num_vars
        num_vars_padded = max(num_vars_padded, num_inputs + 1);

        // ensure that num_vars_padded a power of two
        if num_vars_padded.next_power_of_two() != num_vars_padded {
          num_vars_padded = num_vars_padded.next_power_of_two();
        }
        num_vars_padded
      };

      let num_cons_padded = {
        let mut num_cons_padded = num_cons;

        // ensure that num_cons_padded is at least 2
        if num_cons_padded == 0 || num_cons_padded == 1 {
          num_cons_padded = 2;
        }

        // ensure that num_cons_padded is power of 2
        if num_cons.next_power_of_two() != num_cons {
          num_cons_padded = num_cons.next_power_of_two();
        }
        num_cons_padded
      };

      (num_vars_padded, num_cons_padded)
    };

    let bytes_to_scalar =
      |tups: &[(usize, usize, Vec<u8>)]| -> Result<Vec<(usize, usize, F)>, R1CSError> {
        let mut mat: Vec<(usize, usize, F)> = Vec::new();
        for (row, col, val_bytes) in tups {
          // row must be smaller than num_cons
          if *row >= num_cons {
            return Err(R1CSError::InvalidIndex);
          }

          // col must be smaller than num_vars + 1 + num_inputs
          if *col >= num_vars + 1 + num_inputs {
            return Err(R1CSError::InvalidIndex);
          }

          let val = F::from_random_bytes(val_bytes.as_slice());
          if let Some(v) = val {
            // if col >= num_vars, it means that it is referencing a 1 or input in the satisfying
            // assignment
            if *col >= num_vars {
              mat.push((*row, *col + num_vars_padded - num_vars, v));
            } else {
              mat.push((*row, *col, v));
            }
          } else {
            return Err(R1CSError::InvalidScalar);
          }
        }

        // pad with additional constraints up until num_cons_padded if the original constraints were 0 or 1
        // we do not need to pad otherwise because the dummy constraints are implicit in the sum-check protocol
        if num_cons == 0 || num_cons == 1 {
          for i in tups.len()..num_cons_padded {
            mat.push((i, num_vars, F::zero()));
          }
        }

        Ok(mat)
      };

    let A_scalar = bytes_to_scalar(A);
    if A_scalar.is_err() {
      return Err(A_scalar.err().unwrap());
    }

    let B_scalar = bytes_to_scalar(B);
    if B_scalar.is_err() {
      return Err(B_scalar.err().unwrap());
    }

    let C_scalar = bytes_to_scalar(C);
    if C_scalar.is_err() {
      return Err(C_scalar.err().unwrap());
    }

    let inst = R1CSInstance::new(
      num_cons_padded,
      num_vars_padded,
      num_inputs,
      &A_scalar.unwrap(),
      &B_scalar.unwrap(),
      &C_scalar.unwrap(),
    );

    let digest = inst.get_digest();

    Ok(Instance { inst, digest })
  }

  /// Checks if a given R1CSInstance is satisfiable with a given variables and inputs assignments
  pub fn is_sat(
    &self,
    vars: &VarsAssignment<F>,
    inputs: &InputsAssignment<F>,
  ) -> Result<bool, R1CSError> {
    if vars.assignment.len() > self.inst.get_num_vars() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    if inputs.assignment.len() != self.inst.get_num_inputs() {
      return Err(R1CSError::InvalidNumberOfInputs);
    }

    // we might need to pad variables
    let padded_vars = {
      let num_padded_vars = self.inst.get_num_vars();
      let num_vars = vars.assignment.len();
      if num_padded_vars > num_vars {
        vars.pad(num_padded_vars)
      } else {
        vars.clone()
      }
    };

    Ok(
      self
        .inst
        .is_sat(&padded_vars.assignment, &inputs.assignment),
    )
  }

  /// Constructs a new synthetic R1CS `Instance` and an associated satisfying assignment
  pub fn produce_synthetic_r1cs(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
  ) -> (Instance<F>, VarsAssignment<F>, InputsAssignment<F>) {
    let (inst, vars, inputs) = R1CSInstance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);
    let digest = inst.get_digest();
    (
      Instance { inst, digest },
      VarsAssignment { assignment: vars },
      InputsAssignment { assignment: inputs },
    )
  }
}

#[inline]
pub(crate) fn dot_product<F: PrimeField>(a: &[F], b: &[F]) -> F {
  let mut res = F::zero();
  for i in 0..a.len() {
    res += a[i] * &b[i];
  }
  res
}

#[cfg(test)]
mod tests {

  use super::*;

  type F = ark_bls12_377::Fr;

  #[test]
  pub fn check_r1cs_invalid_index() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let A = vec![(0, 0, zero.to_vec())];
    let B = vec![(100, 1, zero.to_vec())];
    let C = vec![(1, 1, zero.to_vec())];

    let inst = Instance::<F>::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidIndex));
  }

  #[test]
  pub fn check_r1cs_invalid_scalar() {
    let num_cons = 4;
    let num_vars = 8;
    let num_inputs = 1;

    let zero: [u8; 32] = [
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0,
    ];

    let larger_than_mod = [
      3, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8, 216,
      57, 51, 72, 125, 157, 41, 83, 167, 237, 115,
    ];

    let A = vec![(0, 0, zero.to_vec())];
    let B = vec![(1, 1, larger_than_mod.to_vec())];
    let C = vec![(1, 1, zero.to_vec())];

    let inst = Instance::<F>::new(num_cons, num_vars, num_inputs, &A, &B, &C);
    assert!(inst.is_err());
    assert_eq!(inst.err(), Some(R1CSError::InvalidScalar));
  }
}
