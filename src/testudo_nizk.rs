// use std::cmp::max;

// use crate::errors::ProofVerifyError;
// use crate::r1csproof::R1CSVerifierProof;
// use crate::{
//   poseidon_transcript::PoseidonTranscript,
//   r1csproof::{R1CSGens, R1CSProof},
//   transcript::Transcript,
//   InputsAssignment, Instance, VarsAssignment,
// };
// use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
// use ark_crypto_primitives::sponge::Absorb;
// use ark_ec::pairing::Pairing;

// use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

// #[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]

// // TestudoNizk is suitable for uniform circuits where the
// // evaluation of R1CS matrices A, B and C is cheap and can
// // be done by the verifier. For more complex circuits this
// // operation has to be offloaded to the prover.
// pub struct TestudoNizk<E: Pairing> {
//   pub r1cs_verifier_proof: R1CSVerifierProof<E>,
//   pub r: (Vec<E::ScalarField>, Vec<E::ScalarField>),
// }

// pub struct TestudoNizkGens<E: Pairing> {
//   gens_r1cs_sat: R1CSGens<E>,
// }

// impl<E: Pairing> TestudoNizkGens<E> {
//   /// Performs the setup required  by the polynomial commitment PST and Groth16
//   pub fn setup(
//     num_cons: usize,
//     num_vars: usize,
//     num_inputs: usize,
//     poseidon: PoseidonConfig<E::ScalarField>,
//   ) -> Self {
//     // ensure num_vars is a power of 2
//     let num_vars_padded = {
//       let mut num_vars_padded = max(num_vars, num_inputs + 1);
//       if num_vars_padded != num_vars_padded.next_power_of_two() {
//         num_vars_padded = num_vars_padded.next_power_of_two();
//       }
//       num_vars_padded
//     };

//     let num_cons_padded = {
//       let mut num_cons_padded = num_cons;

//       // ensure that num_cons_padded is at least 2
//       if num_cons_padded == 0 || num_cons_padded == 1 {
//         num_cons_padded = 2;
//       }

//       // ensure that num_cons_padded is a power of 2
//       if num_cons.next_power_of_two() != num_cons {
//         num_cons_padded = num_cons.next_power_of_two();
//       }
//       num_cons_padded
//     };

//     let gens_r1cs_sat = R1CSGens::setup(
//       b"gens_r1cs_sat",
//       num_cons_padded,
//       num_vars_padded,
//       num_inputs,
//       poseidon,
//     );
//     TestudoNizkGens { gens_r1cs_sat }
//   }
// }

// impl<E: Pairing> TestudoNizk<E>
// where
//   E::ScalarField: Absorb,
// {
//   // Returns a proof that the R1CS instance is satisfiable
//   pub fn prove(
//     inst: &Instance<E::ScalarField>,
//     vars: VarsAssignment<E::ScalarField>,
//     inputs: &InputsAssignment<E::ScalarField>,
//     gens: &TestudoNizkGens<E>,
//     transcript: &mut PoseidonTranscript<E::ScalarField>,
//     poseidon: PoseidonConfig<E::ScalarField>,
//   ) -> Result<TestudoNizk<E>, ProofVerifyError> {
//     transcript.append_bytes(b"", &inst.digest);

//     let c: E::ScalarField = transcript.challenge_scalar(b"");
//     transcript.new_from_state(&c);

//     // we might need to pad variables
//     let padded_vars = {
//       let num_padded_vars = inst.inst.get_num_vars();
//       let num_vars = vars.assignment.len();
//       if num_padded_vars > num_vars {
//         vars.pad(num_padded_vars)
//       } else {
//         vars
//       }
//     };

//     let (r1cs_sat_proof, rx, ry) = R1CSProof::prove(
//       &inst.inst,
//       padded_vars.assignment,
//       &inputs.assignment,
//       &gens.gens_r1cs_sat,
//       transcript,
//     );

//     let inst_evals = inst.inst.evaluate(&rx, &ry);

//     transcript.new_from_state(&c);
//     let r1cs_verifier_proof = r1cs_sat_proof
//       .prove_verifier(
//         inst.inst.get_num_vars(),
//         inst.inst.get_num_cons(),
//         &inputs.assignment,
//         &inst_evals,
//         transcript,
//         &gens.gens_r1cs_sat,
//         poseidon,
//       )
//       .unwrap();
//     Ok(TestudoNizk {
//       r1cs_verifier_proof,
//       r: (rx, ry),
//     })
//   }

//   // Verifies the satisfiability proof for the R1CS instance. In NIZK mode, the
//   // verifier evaluates matrices A, B and C themselves, which is a linear
//   // operation and hence this is not a SNARK.
//   // However, for highly structured circuits this operation is fast.
//   pub fn verify(
//     &self,
//     gens: &TestudoNizkGens<E>,
//     inst: &Instance<E::ScalarField>,
//     input: &InputsAssignment<E::ScalarField>,
//     transcript: &mut PoseidonTranscript<E::ScalarField>,
//     _poseidon: PoseidonConfig<E::ScalarField>,
//   ) -> Result<bool, ProofVerifyError> {
//     transcript.append_bytes(b"", &inst.digest);
//     let (claimed_rx, claimed_ry) = &self.r;
//     let inst_evals = inst.inst.evaluate(claimed_rx, claimed_ry);

//     let sat_verified = self.r1cs_verifier_proof.verify(
//       (claimed_rx.clone(), claimed_ry.clone()),
//       &input.assignment,
//       &inst_evals,
//       transcript,
//       &gens.gens_r1cs_sat,
//     )?;
//     assert!(sat_verified == true);
//     Ok(sat_verified)
//   }
// }

// #[cfg(test)]
// mod tests {
//   use crate::{
//     parameters::poseidon_params,
//     poseidon_transcript::PoseidonTranscript,
//     testudo_nizk::{TestudoNizk, TestudoNizkGens},
//     Instance,
//   };

//   #[test]
//   pub fn check_testudo_nizk() {
//     let num_vars = 256;
//     let num_cons = num_vars;
//     let num_inputs = 10;

//     type E = ark_bls12_377::Bls12_377;

//     // produce public generators
//     let gens = TestudoNizkGens::<E>::setup(num_cons, num_vars, num_inputs, poseidon_params());

//     // produce a synthetic R1CSInstance
//     let (inst, vars, inputs) = Instance::produce_synthetic_r1cs(num_cons, num_vars, num_inputs);

//     let params = poseidon_params();

//     // produce a proof
//     let mut prover_transcript = PoseidonTranscript::new(&params);
//     let proof =
//       TestudoNizk::prove(&inst, vars, &inputs, &gens, &mut prover_transcript, params).unwrap();

//     // verify the proof
//     let mut verifier_transcript = PoseidonTranscript::new(&poseidon_params());
//     assert!(proof
//       .verify(
//         &gens,
//         &inst,
//         &inputs,
//         &mut verifier_transcript,
//         poseidon_params()
//       )
//       .is_ok());
//   }
// }
