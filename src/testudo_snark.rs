use std::cmp::max;

use crate::errors::ProofVerifyError;
use crate::r1csinstance::{R1CSCommitmentGens, R1CSEvalProof};
use crate::r1csproof::R1CSVerifierProof;

use crate::timer::Timer;
use crate::transcript::TranscriptWriter;
use crate::{
  poseidon_transcript::PoseidonTranscript,
  r1csproof::{R1CSGens, R1CSProof},
  transcript::Transcript,
  InputsAssignment, Instance, VarsAssignment,
};
use crate::{ComputationCommitment, ComputationDecommitment};
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::pairing::Pairing;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TestudoSnark<E: Pairing> {
  pub r1cs_verifier_proof: R1CSVerifierProof<E>,
  pub r1cs_eval_proof: R1CSEvalProof<E>,
  pub inst_evals: (E::ScalarField, E::ScalarField, E::ScalarField),
  pub r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
}

pub struct TestudoSnarkGens<E: Pairing> {
  gens_r1cs_sat: R1CSGens<E>,
  gens_r1cs_eval: R1CSCommitmentGens<E>,
}

impl<E: Pairing> TestudoSnarkGens<E> {
  /// Performs the setups required by the polynomial commitment PST, Groth16
  /// and the computational commitment given the size of the R1CS statement,
  /// `num_nz_entries` specifies the maximum number of non-zero entries in
  ///  any of the three R1CS matrices.
  pub fn setup(
    num_cons: usize,
    num_vars: usize,
    num_inputs: usize,
    num_nz_entries: usize,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Self {
    // ensure num_vars is a power of 2
    let num_vars_padded = {
      let mut num_vars_padded = max(num_vars, num_inputs + 1);
      if num_vars_padded != num_vars_padded.next_power_of_two() {
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

      // ensure that num_cons_padded is a power of 2
      if num_cons.next_power_of_two() != num_cons {
        num_cons_padded = num_cons.next_power_of_two();
      }
      num_cons_padded
    };

    let gens_r1cs_sat = R1CSGens::setup(
      b"gens_r1cs_sat",
      num_cons_padded,
      num_vars_padded,
      num_inputs,
      poseidon,
    );
    let gens_r1cs_eval = R1CSCommitmentGens::setup(
      b"gens_r1cs_eval",
      num_cons_padded,
      num_vars_padded,
      num_inputs,
      num_nz_entries,
    );
    TestudoSnarkGens {
      gens_r1cs_sat,
      gens_r1cs_eval,
    }
  }
}

impl<E: Pairing> TestudoSnark<E>
where
  E::ScalarField: Absorb,
{
  // Constructs the computational commitment, used to prove that the
  // evaluations of matrices A, B and C sent by the prover to the verifier
  // are correct.
  pub fn encode(
    inst: &Instance<E::ScalarField>,
    gens: &TestudoSnarkGens<E>,
  ) -> (
    ComputationCommitment<E::G1>,
    ComputationDecommitment<E::ScalarField>,
  ) {
    let timer_encode = Timer::new("SNARK::encode");
    let (comm, decomm) = inst.inst.commit(&gens.gens_r1cs_eval);
    timer_encode.stop();
    (
      ComputationCommitment { comm },
      ComputationDecommitment { decomm },
    )
  }

  // Returns the Testudo SNARK proof which has two components:
  // * proof that the R1CS instance is satisfiable
  // * proof that the evlauation of matrices A, B and C on point (x,y)
  // resulted from the two rounda of sumcheck are correct
  pub fn prove(
    inst: &Instance<E::ScalarField>,
    comm: &ComputationCommitment<E::G1>,
    decomm: &ComputationDecommitment<E::ScalarField>,
    vars: VarsAssignment<E::ScalarField>,
    inputs: &InputsAssignment<E::ScalarField>,
    gens: &TestudoSnarkGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<TestudoSnark<E>, ProofVerifyError> {
    comm.comm.write_to_transcript(transcript);
    let c: E::ScalarField = transcript.challenge_scalar(b"");
    transcript.new_from_state(&c);

    // we might need to pad variables
    let padded_vars = {
      let num_padded_vars = inst.inst.get_num_vars();
      let num_vars = vars.assignment.len();
      if num_padded_vars > num_vars {
        vars.pad(num_padded_vars)
      } else {
        vars
      }
    };

    let (r1cs_sat_proof, rx, ry) = R1CSProof::prove(
      &inst.inst,
      padded_vars.assignment,
      &inputs.assignment,
      &gens.gens_r1cs_sat,
      transcript,
    );

    // We send evaluations of A, B, C at r = (rx, ry) as claims
    // to enable the verifier complete the first sum-check
    let timer_eval = Timer::new("eval_sparse_polys");
    let inst_evals = {
      let (Ar, Br, Cr) = inst.inst.evaluate(&rx, &ry);
      transcript.append_scalar(b"", &Ar);
      transcript.append_scalar(b"", &Br);
      transcript.append_scalar(b"", &Cr);
      (Ar, Br, Cr)
    };
    timer_eval.stop();

    let timer_eval_proof = Timer::new("r1cs_eval_proof");
    let r1cs_eval_proof = R1CSEvalProof::prove(
      &decomm.decomm,
      &rx,
      &ry,
      &inst_evals,
      &gens.gens_r1cs_eval,
      transcript,
    );
    timer_eval_proof.stop();

    transcript.new_from_state(&c);
    let timer_sat_circuit_verification = Timer::new("r1cs_sat_circuit_verification_proof");
    let r1cs_verifier_proof = r1cs_sat_proof
      .prove_verifier(
        inst.inst.get_num_vars(),
        inst.inst.get_num_cons(),
        &inputs.assignment,
        &inst_evals,
        transcript,
        &gens.gens_r1cs_sat,
        poseidon,
      )
      .unwrap();
    timer_sat_circuit_verification.stop();
    Ok(TestudoSnark {
      r1cs_verifier_proof,
      r1cs_eval_proof,
      inst_evals,
      r: (rx, ry),
    })
  }

  pub fn verify(
    &self,
    gens: &TestudoSnarkGens<E>,
    comm: &ComputationCommitment<E::G1>,
    input: &InputsAssignment<E::ScalarField>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    _poseidon: PoseidonConfig<E::ScalarField>,
  ) -> Result<bool, ProofVerifyError> {
    let timer_sat_verification = Timer::new("r1cs_sat_verification");
    let sat_verified = self.r1cs_verifier_proof.verify(
      &input.assignment,
      &self.inst_evals,
      transcript,
      &gens.gens_r1cs_sat,
    )?;
    timer_sat_verification.stop();
    assert!(sat_verified == true);

    let (Ar, Br, Cr) = &self.inst_evals;
    transcript.append_scalar(b"", Ar);
    transcript.append_scalar(b"", Br);
    transcript.append_scalar(b"", Cr);

    let (rx, ry) = &self.r;
    let timer_eval_verification = Timer::new("r1cs_eval_verification");
    let eval_verified = self.r1cs_eval_proof.verify(
      &comm.comm,
      rx,
      ry,
      &self.inst_evals,
      &gens.gens_r1cs_eval,
      transcript,
    );
    timer_eval_verification.stop();
    Ok(sat_verified && eval_verified.is_ok())
  }
}

#[cfg(test)]
mod tests {

  use crate::ark_std::Zero;
  use crate::{
    parameters::poseidon_params,
    poseidon_transcript::PoseidonTranscript,
    testudo_snark::{TestudoSnark, TestudoSnarkGens},
    InputsAssignment, Instance, VarsAssignment,
  };
  use ark_ff::{BigInteger, One, PrimeField};

  #[test]
  pub fn check_testudo_snark() {
    let num_vars = 256;
    let num_cons = num_vars;
    let num_inputs = 10;

    type E = ark_bls12_377::Bls12_377;

    // produce public generators
    let gens =
      TestudoSnarkGens::<E>::setup(num_cons, num_vars, num_inputs, num_cons, poseidon_params());

    // produce a synthetic R1CSInstance
    let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

    // create a commitment to R1CSInstance
    let (comm, decomm) = TestudoSnark::encode(&inst, &gens);

    let params = poseidon_params();

    // produce a proof
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof = TestudoSnark::prove(
      &inst,
      &comm,
      &decomm,
      vars,
      &inputs,
      &gens,
      &mut prover_transcript,
      params,
    )
    .unwrap();

    // verify the proof
    let mut verifier_transcript = PoseidonTranscript::new(&poseidon_params());
    assert!(proof
      .verify(
        &gens,
        &comm,
        &inputs,
        &mut verifier_transcript,
        poseidon_params()
      )
      .is_ok());
  }

  #[test]
  fn test_padded_constraints() {
    type F = ark_bls12_377::Fr;
    type E = ark_bls12_377::Bls12_377;
    // parameters of the R1CS instance
    let num_cons = 1;
    let num_vars = 0;
    let num_inputs = 3;
    let num_non_zero_entries = 3;

    // We will encode the above constraints into three matrices, where
    // the coefficients in the matrix are in the little-endian byte order
    let mut A: Vec<(usize, usize, Vec<u8>)> = Vec::new();
    let mut B: Vec<(usize, usize, Vec<u8>)> = Vec::new();
    let mut C: Vec<(usize, usize, Vec<u8>)> = Vec::new();

    // Create a^2 + b + 13
    A.push((0, num_vars + 2, (F::one().into_bigint().to_bytes_le()))); // 1*a
    B.push((0, num_vars + 2, F::one().into_bigint().to_bytes_le())); // 1*a
    C.push((0, num_vars + 1, F::one().into_bigint().to_bytes_le())); // 1*z
    C.push((0, num_vars, (-F::from(13u64)).into_bigint().to_bytes_le())); // -13*1
    C.push((0, num_vars + 3, (-F::one()).into_bigint().to_bytes_le())); // -1*b

    // Var Assignments (Z_0 = 16 is the only output)
    let vars = vec![F::zero().into_bigint().to_bytes_le(); num_vars];

    // create an InputsAssignment (a = 1, b = 2)
    let mut inputs = vec![F::zero().into_bigint().to_bytes_le(); num_inputs];
    inputs[0] = F::from(16u64).into_bigint().to_bytes_le();
    inputs[1] = F::from(1u64).into_bigint().to_bytes_le();
    inputs[2] = F::from(2u64).into_bigint().to_bytes_le();

    let assignment_inputs = InputsAssignment::<F>::new(&inputs).unwrap();
    let assignment_vars = VarsAssignment::new(&vars).unwrap();

    // Check if instance is satisfiable
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();
    let res = inst.is_sat(&assignment_vars, &assignment_inputs);
    assert!(res.unwrap(), "should be satisfied");

    // Testudo public params
    let gens = TestudoSnarkGens::<E>::setup(
      num_cons,
      num_vars,
      num_inputs,
      num_non_zero_entries,
      poseidon_params(),
    );

    // create a commitment to the R1CS instance
    let (comm, decomm) = TestudoSnark::encode(&inst, &gens);

    let params = poseidon_params();

    // produce a TestudoSnark
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof = TestudoSnark::prove(
      &inst,
      &comm,
      &decomm,
      assignment_vars.clone(),
      &assignment_inputs,
      &gens,
      &mut prover_transcript,
      poseidon_params(),
    )
    .unwrap();

    // verify the TestudoSnark
    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(
        &gens,
        &comm,
        &assignment_inputs,
        &mut verifier_transcript,
        poseidon_params()
      )
      .is_ok());
  }
}
