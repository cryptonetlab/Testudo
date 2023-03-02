#![allow(clippy::too_many_arguments)]
use super::commitments::{MultiCommitGens, PedersenCommit};
use super::errors::ProofVerifyError;
use crate::ark_std::UniformRand;
use crate::math::Math;
use crate::poseidon_transcript::PoseidonTranscript;
use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::CurveGroup;

use ark_serialize::*;
use std::ops::Mul;

mod bullet;
use bullet::BulletReductionProof;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProofGens<G: CurveGroup> {
  n: usize,
  pub gens_n: MultiCommitGens<G>,
  pub gens_1: MultiCommitGens<G>,
}

impl<G: CurveGroup> DotProductProofGens<G> {
  pub fn new(n: usize, label: &[u8]) -> Self {
    let (gens_n, gens_1) = MultiCommitGens::<G>::new(n + 1, label).split_at(n);
    DotProductProofGens { n, gens_n, gens_1 }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DotProductProofLog<G: CurveGroup> {
  bullet_reduction_proof: BulletReductionProof<G>,
  delta: G,
  beta: G,
  z1: G::ScalarField,
  z2: G::ScalarField,
}

impl<G> DotProductProofLog<G>
where
  G: CurveGroup,
  G::ScalarField: Absorb,
{
  pub fn prove(
    gens: &DotProductProofGens<G>,
    transcript: &mut PoseidonTranscript<G::ScalarField>,
    x_vec: &[G::ScalarField],
    blind_x: &G::ScalarField,
    a_vec: &[G::ScalarField],
    y: &G::ScalarField,
    blind_y: &G::ScalarField,
  ) -> (Self, G, G) {
    // transcript.append_protocol_name(DotProductProofLog::protocol_name());

    let n = x_vec.len();
    assert_eq!(x_vec.len(), a_vec.len());
    assert_eq!(gens.n, n);

    // produce randomness for generating a proof
    let d = G::ScalarField::rand(&mut rand::thread_rng());
    let r_delta = G::ScalarField::rand(&mut rand::thread_rng()).into();
    let r_beta = G::ScalarField::rand(&mut rand::thread_rng()).into();
    let blinds_vec = {
      (0..2 * n.log_2())
        .map(|_| {
          (
            G::ScalarField::rand(&mut rand::thread_rng()).into(),
            G::ScalarField::rand(&mut rand::thread_rng()).into(),
          )
        })
        .collect::<Vec<(G::ScalarField, G::ScalarField)>>()
    };

    let Cx = PedersenCommit::commit_slice(x_vec, blind_x, &gens.gens_n);
    transcript.append_point(b"", &Cx);

    let Cy = PedersenCommit::commit_scalar(y, blind_y, &gens.gens_1);
    transcript.append_point(b"", &Cy);
    transcript.append_scalar_vector(b"", &a_vec);

    let blind_Gamma = (*blind_x) + blind_y;
    let (bullet_reduction_proof, _Gamma_hat, x_hat, a_hat, g_hat, rhat_Gamma) =
      BulletReductionProof::<G>::prove(
        transcript,
        &gens.gens_1.G[0],
        &gens.gens_n.G,
        &gens.gens_n.h,
        x_vec,
        a_vec,
        &blind_Gamma,
        &blinds_vec,
      );
    let y_hat = x_hat * a_hat;

    let delta = {
      let gens_hat = MultiCommitGens {
        n: 1,
        G: vec![g_hat.into_affine()],
        h: gens.gens_1.h,
      };
      PedersenCommit::commit_scalar(&d, &r_delta, &gens_hat)
    };
    transcript.append_point(b"", &delta);

    let beta = PedersenCommit::commit_scalar(&d, &r_beta, &gens.gens_1);
    transcript.append_point(b"", &beta);

    let c: G::ScalarField = transcript.challenge_scalar(b"");

    let z1 = d + c * y_hat;
    let z2 = a_hat * (c * rhat_Gamma + r_beta) + r_delta;

    (
      Self {
        bullet_reduction_proof,
        delta,
        beta,
        z1,
        z2,
      },
      Cx,
      Cy,
    )
  }

  pub fn verify(
    &self,
    n: usize,
    gens: &DotProductProofGens<G>,
    transcript: &mut PoseidonTranscript<G::ScalarField>,
    a: &[G::ScalarField],
    Cx: &G,
    Cy: &G,
  ) -> Result<(), ProofVerifyError> {
    assert_eq!(gens.n, n);
    assert_eq!(a.len(), n);

    // transcript.append_protocol_name(DotProductProofLog::protocol_name());
    // Cx.write_to_transcript( transcript);
    // Cy.write_to_transcript( transcript);
    // a.write_to_transcript( transcript);

    transcript.append_point(b"", Cx);
    transcript.append_point(b"", Cy);
    transcript.append_scalar_vector(b"", &a);

    let Gamma = Cx.add(Cy);

    let (g_hat, Gamma_hat, a_hat) =
      self
        .bullet_reduction_proof
        .verify(n, a, transcript, &Gamma, &gens.gens_n.G)?;
    // self.delta.write_to_transcript( transcript);
    // self.beta.write_to_transcript( transcript);

    transcript.append_point(b"", &self.delta);
    transcript.append_point(b"", &self.beta);

    let c = transcript.challenge_scalar(b"");

    let c_s = &c;
    let beta_s = self.beta;
    let a_hat_s = &a_hat;
    let delta_s = self.delta;
    let z1_s = &self.z1;
    let z2_s = &self.z2;

    let lhs = (Gamma_hat.mul(c_s) + beta_s).mul(a_hat_s) + delta_s;
    let rhs = (g_hat + gens.gens_1.G[0].mul(a_hat_s)).mul(z1_s) + gens.gens_1.h.mul(z2_s);
    assert_eq!(lhs, rhs);

    if lhs == rhs {
      Ok(())
    } else {
      Err(ProofVerifyError::InternalError)
    }
  }
}

#[cfg(test)]
mod tests {

  use crate::parameters::PoseidonConfiguration;

  use super::*;
  use ark_ec::CurveGroup;
  use ark_std::UniformRand;

  #[test]
  fn check_dotproductproof_log_blst() {
    check_dotproductproof_log::<ark_bls12_381::G1Projective>();
  }

  #[test]
  fn check_dotproductproof_log_arkworks_bls12_381() {
    check_dotproductproof_log::<ark_bls12_381::G1Projective>();
  }

  fn check_dotproductproof_log<G: CurveGroup>()
  where
    G::ScalarField: PoseidonConfiguration + Absorb,
  {
    let mut rng = ark_std::rand::thread_rng();

    let n = 1024;

    let gens = DotProductProofGens::<G>::new(n, b"test-1024");

    let x: Vec<G::ScalarField> = (0..n).map(|_i| G::ScalarField::rand(&mut rng)).collect();
    let a: Vec<G::ScalarField> = (0..n).map(|_i| G::ScalarField::rand(&mut rng)).collect();
    let y = crate::dot_product(&x, &a);

    let r_x = G::ScalarField::rand(&mut rng);
    let r_y = G::ScalarField::rand(&mut rng);

    let params = G::ScalarField::poseidon_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let (proof, Cx, Cy) =
      DotProductProofLog::<G>::prove(&gens, &mut prover_transcript, &x, &r_x, &a, &y, &r_y);

    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(n, &gens, &mut verifier_transcript, &a, &Cx, &Cy)
      .is_ok());
  }
}
