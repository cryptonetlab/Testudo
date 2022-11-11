use crate::{
  group::{CompressedGroup, Fr},
};

use super::scalar::Scalar;





// use ark_r1cs_std::prelude::*;
use ark_sponge::{
  constraints::{CryptographicSpongeVar},
  poseidon::{PoseidonParameters, PoseidonSponge},
  CryptographicSponge,
};

#[derive(Clone)]
/// TODO
pub struct PoseidonTranscript {
  sponge: PoseidonSponge<Fr>,
  params: PoseidonParameters<Fr>,
}

impl PoseidonTranscript {
  /// create a new transcript
  pub fn new(params: &PoseidonParameters<Fr>) -> Self {
    let sponge = PoseidonSponge::new(params);
    PoseidonTranscript {
      sponge: sponge,
      params: params.clone(),
    }
  }

  pub fn new_from_state(&mut self, challenge: &Scalar) {
    self.sponge = PoseidonSponge::new(&self.params);
    self.append_scalar(&challenge);
  }

  pub fn append_u64(&mut self, x: u64) {
    self.sponge.absorb(&x);
  }

  pub fn append_bytes(&mut self, x: &Vec<u8>) {
    self.sponge.absorb(x);
  }

  pub fn append_scalar(&mut self, scalar: &Scalar) {
    self.sponge.absorb(&scalar);
  }

  pub fn append_point(&mut self, point: &CompressedGroup) {
    self.sponge.absorb(&point.0);
  }

  pub fn append_scalar_vector(&mut self, scalars: &Vec<Scalar>) {
    for scalar in scalars.iter() {
      self.append_scalar(&scalar);
    }
  }

  pub fn challenge_scalar(&mut self) -> Scalar {
    let scalar = self.sponge.squeeze_field_elements(1).remove(0);
    scalar
  }

  pub fn challenge_vector(&mut self, len: usize) -> Vec<Scalar> {
    let challenges = self.sponge.squeeze_field_elements(len);
    challenges
  }
}

pub trait AppendToPoseidon {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript);
}

impl AppendToPoseidon for CompressedGroup {
  fn append_to_poseidon(&self, transcript: &mut PoseidonTranscript) {
    transcript.append_point(self);
  }
}
