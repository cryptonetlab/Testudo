use super::scalar::Scalar;
use crate::group::CompressedGroup;
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use merlin::Transcript;

pub trait ProofTranscript {
  fn append_protocol_name(&mut self, protocol_name: &'static [u8]);
  fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar);
  fn append_point(&mut self, label: &'static [u8], point: &CompressedGroup);
  fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar;
  fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<Scalar>;
}

impl ProofTranscript for Transcript {
  fn append_protocol_name(&mut self, protocol_name: &'static [u8]) {
    self.append_message(b"protocol-name", protocol_name);
  }

  fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar) {
    self.append_message(label, &scalar.into_repr().to_bytes_le().as_slice());
  }

  fn append_point(&mut self, label: &'static [u8], point: &CompressedGroup) {
    let mut point_encoded = Vec::new();
    point.serialize(&mut point_encoded).unwrap();
    self.append_message(label, point_encoded.as_slice());
  }

  fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar {
    let mut buf = [0u8; 64];
    self.challenge_bytes(label, &mut buf);
    Scalar::from_le_bytes_mod_order(&buf)
  }

  fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<Scalar> {
    (0..len)
      .map(|_i| self.challenge_scalar(label))
      .collect::<Vec<Scalar>>()
  }
}

pub trait AppendToTranscript {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript);
}

impl AppendToTranscript for Scalar {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_scalar(label, self);
  }
}

impl AppendToTranscript for [Scalar] {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_message(label, b"begin_append_vector");
    for item in self {
      transcript.append_scalar(label, item);
    }
    transcript.append_message(label, b"end_append_vector");
  }
}

impl AppendToTranscript for CompressedGroup {
  fn append_to_transcript(&self, label: &'static [u8], transcript: &mut Transcript) {
    transcript.append_point(label, self);
  }
}
