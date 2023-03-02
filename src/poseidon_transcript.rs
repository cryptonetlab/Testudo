use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::{
  poseidon::{PoseidonConfig, PoseidonSponge},
  Absorb, CryptographicSponge,
};
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_serialize::Compress;
#[derive(Clone)]
/// TODO
pub struct PoseidonTranscript<F: PrimeField> {
  sponge: PoseidonSponge<F>,
  params: PoseidonConfig<F>,
}

impl<F: PrimeField> Transcript for PoseidonTranscript<F> {
  fn domain_sep(&mut self) {
    self.sponge.absorb(&b"testudo".to_vec());
  }

  fn append<S: CanonicalSerialize>(&mut self, _label: &'static [u8], point: &S) {
    let mut buf = Vec::new();
    point
      .serialize_with_mode(&mut buf, Compress::Yes)
      .expect("serialization failed");
    self.sponge.absorb(&buf);
  }

  fn challenge_scalar<FF: PrimeField>(&mut self, _label: &'static [u8]) -> FF {
    self.sponge.squeeze_field_elements(1).remove(0)
  }
}

impl<F: PrimeField> PoseidonTranscript<F> {
  /// create a new transcript
  pub fn new(params: &PoseidonConfig<F>) -> Self {
    let sponge = PoseidonSponge::new(params);
    PoseidonTranscript {
      sponge,
      params: params.clone(),
    }
  }
}

impl<F: PrimeField + Absorb> PoseidonTranscript<F> {
  pub fn new_from_state(&mut self, challenge: &F) {
    self.sponge = PoseidonSponge::new(&self.params.clone());
    self.append_scalar(b"", challenge);
  }
}

impl<F: PrimeField> PoseidonTranscript<F> {
  pub fn append_u64(&mut self, _label: &'static [u8], x: u64) {
    self.sponge.absorb(&x);
  }

  pub fn append_bytes(&mut self, _label: &'static [u8], x: &Vec<u8>) {
    self.sponge.absorb(x);
  }

  pub fn append_scalar<T: PrimeField + Absorb>(&mut self, _label: &'static [u8], scalar: &T) {
    self.sponge.absorb(&scalar);
  }

  pub fn append_point<G>(&mut self, _label: &'static [u8], point: &G)
  where
    G: CurveGroup,
  {
    let mut point_encoding = Vec::new();
    point
      .serialize_with_mode(&mut point_encoding, Compress::Yes)
      .unwrap();
    self.sponge.absorb(&point_encoding);
  }

  pub fn append_scalar_vector<T: PrimeField + Absorb>(
    &mut self,
    _label: &'static [u8],
    scalars: &[T],
  ) {
    for scalar in scalars.iter() {
      self.append_scalar(b"", scalar);
    }
  }

  pub fn append_gt<E>(&mut self, _label: &'static [u8], g_t: &E::TargetField)
  where
    E: Pairing,
  {
    let mut bytes = Vec::new();
    g_t.serialize_with_mode(&mut bytes, Compress::Yes).unwrap();
    self.append_bytes(b"", &bytes);
  }
}

pub trait TranscriptWriter<F: PrimeField> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<F>);
}

#[cfg(test)]
mod test {
  use ark_bls12_381::Fr;
  use ark_ff::PrimeField;
  use poseidon_paramgen;

  use super::*;
  use crate::ark_std::UniformRand;
  use crate::parameters::PoseidonConfiguration;

  #[test]
  fn poseidon_compatibility() {
    let mut f1 = PoseidonTranscript::new(&ark_bls12_381::Fr::poseidon_params());
    let mut f2 = PoseidonTranscript::new(&ark_blst::Scalar::poseidon_params());

    let r1 = ark_bls12_381::Fr::rand(&mut rand::thread_rng());
    let r2 = ark_blst::Scalar::from(r1);

    f1.append_scalar(b"", &r1);
    f2.append_scalar(b"", &r2);

    let c1: ark_bls12_381::Fr = f1.challenge_scalar(b"");
    let c2: ark_blst::Scalar = f2.challenge_scalar(b"");

    let c22 = ark_blst::Scalar::from(c1);
    assert!(c2 == c22);
  }
  #[test]
  fn poseidon_parameters_generation() {
    print_modulus::<Fr>();
    println!(
      "{}",
      poseidon_paramgen::poseidon_build::compile::<Fr>(128, vec![2], Fr::MODULUS, true)
    );
  }

  fn print_modulus<F: PrimeField>() {
    println!("modulus: {:?}", F::MODULUS);
  }
}
