#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use super::dense_mlpoly::DensePolynomial;
use super::errors::ProofVerifyError;
use crate::poseidon_transcript::{PoseidonTranscript, TranscriptWriter};
use crate::transcript::Transcript;

use super::unipoly::UniPoly;
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;

use ark_serialize::*;

use itertools::izip;

use ark_ec::pairing::Pairing;

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct SumcheckInstanceProof<F: PrimeField> {
  pub polys: Vec<UniPoly<F>>,
}

impl<F: PrimeField + Absorb> SumcheckInstanceProof<F> {
  pub fn new(polys: Vec<UniPoly<F>>) -> Self {
    SumcheckInstanceProof { polys }
  }

  pub fn verify(
    &self,
    claim: F,
    num_rounds: usize,
    degree_bound: usize,
    transcript: &mut PoseidonTranscript<F>,
  ) -> Result<(F, Vec<F>), ProofVerifyError> {
    let mut e = claim;
    let mut r: Vec<F> = Vec::new();

    // verify that there is a univariate polynomial for each round
    assert_eq!(self.polys.len(), num_rounds);
    for i in 0..self.polys.len() {
      let poly = self.polys[i].clone();

      // verify degree bound
      assert_eq!(poly.degree(), degree_bound);
      // check if G_k(0) + G_k(1) = e

      assert_eq!(poly.eval_at_zero() + poly.eval_at_one(), e);

      // append the prover's message to the transcript
      poly.write_to_transcript(transcript);

      //derive the verifier's challenge for the next round
      let r_i = transcript.challenge_scalar(b"");

      r.push(r_i);

      // evaluate the claimed degree-ell polynomial at r_i
      e = poly.evaluate(&r_i);
    }

    Ok((e, r))
  }
}

impl<F: PrimeField + Absorb> SumcheckInstanceProof<F> {
  pub fn prove_cubic_with_additive_term<C, E>(
    claim: &F,
    num_rounds: usize,
    poly_tau: &mut DensePolynomial<F>,
    poly_A: &mut DensePolynomial<F>,
    poly_B: &mut DensePolynomial<F>,
    poly_C: &mut DensePolynomial<F>,
    comb_func: C,
    transcript: &mut PoseidonTranscript<E::BaseField>,
  ) -> (Self, Vec<F>, Vec<F>)
  where
    C: Fn(&F, &F, &F, &F) -> F,
    E: Pairing,
  {
    let mut e = *claim;
    let mut r: Vec<F> = Vec::new();
    let mut cubic_polys: Vec<UniPoly<F>> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = F::zero();
      let mut eval_point_2 = F::zero();
      let mut eval_point_3 = F::zero();

      let len = poly_tau.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_tau[i], &poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_tau_bound_point = poly_tau[len + i] + poly_tau[len + i] - poly_tau[i];
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];

        eval_point_2 += comb_func(
          &poly_tau_bound_point,
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_tau_bound_point = poly_tau_bound_point + poly_tau[len + i] - poly_tau[i];
        let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];

        eval_point_3 += comb_func(
          &poly_tau_bound_point,
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      //poly.write_to_transcript(transcript);

      for i in 0..poly.coeffs.len() {
        transcript.append_scalar(b"", &poly.coeffs[i]);
      }
      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      poly_tau.bound_poly_var_top(&r_j);
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);

      e = poly.evaluate(&r_j);
      cubic_polys.push(poly);
    }
    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_tau[0], poly_A[0], poly_B[0], poly_C[0]],
    )
  }
  pub fn prove_cubic<C>(
    claim: &F,
    num_rounds: usize,
    poly_A: &mut DensePolynomial<F>,
    poly_B: &mut DensePolynomial<F>,
    poly_C: &mut DensePolynomial<F>,
    comb_func: C,
    transcript: &mut PoseidonTranscript<F>,
  ) -> (Self, Vec<F>, Vec<F>)
  where
    C: Fn(&F, &F, &F) -> F,
  {
    let mut e = *claim;
    let mut r: Vec<F> = Vec::new();
    let mut cubic_polys: Vec<UniPoly<F>> = Vec::new();
    for _j in 0..num_rounds {
      let mut eval_point_0 = F::zero();
      let mut eval_point_2 = F::zero();
      let mut eval_point_3 = F::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
        eval_point_2 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );

        // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
        let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
        let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];

        eval_point_3 += comb_func(
          &poly_A_bound_point,
          &poly_B_bound_point,
          &poly_C_bound_point,
        );
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2, eval_point_3];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.write_to_transcript(transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"");
      r.push(r_j);
      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      poly_C.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      cubic_polys.push(poly);
    }

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      vec![poly_A[0], poly_B[0], poly_C[0]],
    )
  }

  pub fn prove_cubic_batched<C>(
    claim: &F,
    num_rounds: usize,
    poly_vec_par: (
      &mut Vec<&mut DensePolynomial<F>>,
      &mut Vec<&mut DensePolynomial<F>>,
      &mut DensePolynomial<F>,
    ),
    poly_vec_seq: (
      &mut Vec<&mut DensePolynomial<F>>,
      &mut Vec<&mut DensePolynomial<F>>,
      &mut Vec<&mut DensePolynomial<F>>,
    ),
    coeffs: &[F],
    comb_func: C,
    transcript: &mut PoseidonTranscript<F>,
  ) -> (Self, Vec<F>, (Vec<F>, Vec<F>, F), (Vec<F>, Vec<F>, Vec<F>))
  where
    C: Fn(&F, &F, &F) -> F,
  {
    let (poly_A_vec_par, poly_B_vec_par, poly_C_par) = poly_vec_par;
    let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;

    //let (poly_A_vec_seq, poly_B_vec_seq, poly_C_vec_seq) = poly_vec_seq;
    let mut e = *claim;
    let mut r: Vec<F> = Vec::new();
    let mut cubic_polys: Vec<UniPoly<F>> = Vec::new();

    for _j in 0..num_rounds {
      let mut evals: Vec<(F, F, F)> = Vec::new();

      for (poly_A, poly_B) in poly_A_vec_par.iter().zip(poly_B_vec_par.iter()) {
        let mut eval_point_0 = F::zero();
        let mut eval_point_2 = F::zero();
        let mut eval_point_3 = F::zero();

        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C_par[i]);

          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_par[len + i] + poly_C_par[len + i] - poly_C_par[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );

          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C_par[len + i] - poly_C_par[i];

          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }

        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter(),
        poly_B_vec_seq.iter(),
        poly_C_vec_seq.iter()
      ) {
        let mut eval_point_0 = F::zero();
        let mut eval_point_2 = F::zero();
        let mut eval_point_3 = F::zero();
        let len = poly_A.len() / 2;
        for i in 0..len {
          // eval 0: bound_func is A(low)
          eval_point_0 += comb_func(&poly_A[i], &poly_B[i], &poly_C[i]);
          // eval 2: bound_func is -A(low) + 2*A(high)
          let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C[len + i] + poly_C[len + i] - poly_C[i];
          eval_point_2 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
          // eval 3: bound_func is -2A(low) + 3A(high); computed incrementally with bound_func applied to eval(2)
          let poly_A_bound_point = poly_A_bound_point + poly_A[len + i] - poly_A[i];
          let poly_B_bound_point = poly_B_bound_point + poly_B[len + i] - poly_B[i];
          let poly_C_bound_point = poly_C_bound_point + poly_C[len + i] - poly_C[i];
          eval_point_3 += comb_func(
            &poly_A_bound_point,
            &poly_B_bound_point,
            &poly_C_bound_point,
          );
        }
        evals.push((eval_point_0, eval_point_2, eval_point_3));
      }

      let evals_combined_0 = (0..evals.len()).map(|i| evals[i].0 * coeffs[i]).sum();
      let evals_combined_2 = (0..evals.len()).map(|i| evals[i].1 * coeffs[i]).sum();
      let evals_combined_3 = (0..evals.len()).map(|i| evals[i].2 * coeffs[i]).sum();

      let evals = vec![
        evals_combined_0,
        e - evals_combined_0,
        evals_combined_2,
        evals_combined_3,
      ];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      poly.write_to_transcript(transcript);

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      for (poly_A, poly_B) in poly_A_vec_par.iter_mut().zip(poly_B_vec_par.iter_mut()) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
      }
      poly_C_par.bound_poly_var_top(&r_j);

      for (poly_A, poly_B, poly_C) in izip!(
        poly_A_vec_seq.iter_mut(),
        poly_B_vec_seq.iter_mut(),
        poly_C_vec_seq.iter_mut()
      ) {
        poly_A.bound_poly_var_top(&r_j);
        poly_B.bound_poly_var_top(&r_j);
        poly_C.bound_poly_var_top(&r_j);
      }

      e = poly.evaluate(&r_j);
      cubic_polys.push(poly);
    }

    let poly_A_par_final = (0..poly_A_vec_par.len())
      .map(|i| poly_A_vec_par[i][0])
      .collect();
    let poly_B_par_final = (0..poly_B_vec_par.len())
      .map(|i| poly_B_vec_par[i][0])
      .collect();
    let claims_prod = (poly_A_par_final, poly_B_par_final, poly_C_par[0]);

    let poly_A_seq_final = (0..poly_A_vec_seq.len())
      .map(|i| poly_A_vec_seq[i][0])
      .collect();
    let poly_B_seq_final = (0..poly_B_vec_seq.len())
      .map(|i| poly_B_vec_seq[i][0])
      .collect();
    let poly_C_seq_final = (0..poly_C_vec_seq.len())
      .map(|i| poly_C_vec_seq[i][0])
      .collect();
    let claims_dotp = (poly_A_seq_final, poly_B_seq_final, poly_C_seq_final);

    (
      SumcheckInstanceProof::new(cubic_polys),
      r,
      claims_prod,
      claims_dotp,
    )
  }

  pub fn prove_quad<C, E>(
    claim: &F,
    num_rounds: usize,
    poly_A: &mut DensePolynomial<F>,
    poly_B: &mut DensePolynomial<F>,
    comb_func: C,
    transcript: &mut PoseidonTranscript<E::BaseField>,
  ) -> (Self, Vec<F>, Vec<F>)
  where
    C: Fn(&F, &F) -> F,
    E: Pairing,
  {
    let mut e = *claim;
    let mut r: Vec<F> = Vec::new();
    let mut quad_polys: Vec<UniPoly<F>> = Vec::new();

    for _j in 0..num_rounds {
      let mut eval_point_0 = F::zero();
      let mut eval_point_2 = F::zero();

      let len = poly_A.len() / 2;
      for i in 0..len {
        // eval 0: bound_func is A(low)
        eval_point_0 += comb_func(&poly_A[i], &poly_B[i]);

        // eval 2: bound_func is -A(low) + 2*A(high)
        let poly_A_bound_point = poly_A[len + i] + poly_A[len + i] - poly_A[i];
        let poly_B_bound_point = poly_B[len + i] + poly_B[len + i] - poly_B[i];
        eval_point_2 += comb_func(&poly_A_bound_point, &poly_B_bound_point);
      }

      let evals = vec![eval_point_0, e - eval_point_0, eval_point_2];
      let poly = UniPoly::from_evals(&evals);

      // append the prover's message to the transcript
      //poly.write_to_transcript(transcript);
      for i in 0..poly.coeffs.len() {
        transcript.append_scalar(b"", &poly.coeffs[i]);
      }

      //derive the verifier's challenge for the next round
      let r_j = transcript.challenge_scalar(b"");
      r.push(r_j);

      // bound all tables to the verifier's challenege
      poly_A.bound_poly_var_top(&r_j);
      poly_B.bound_poly_var_top(&r_j);
      e = poly.evaluate(&r_j);
      quad_polys.push(poly);
    }

    (
      SumcheckInstanceProof::new(quad_polys),
      r,
      vec![poly_A[0], poly_B[0]],
    )
  }
}
