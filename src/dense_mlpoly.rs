#![allow(clippy::too_many_arguments)]

use super::commitments::{MultiCommitGens, PedersenCommit};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::nizk::{DotProductProofGens, DotProductProofLog};
use crate::poseidon_transcript::{PoseidonTranscript, TranscriptWriter};
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::scalar_mul::variable_base::VariableBaseMSM;
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::{PrimeField, Zero};
use ark_poly::MultilinearExtension;
use ark_poly_commit::multilinear_pc::data_structures::{CommitterKey, VerifierKey};
use ark_poly_commit::multilinear_pc::MultilinearPC;
use ark_serialize::*;
use core::ops::Index;
#[cfg(feature = "multicore")]
use rayon::prelude::*;
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};
// TODO: integrate the DenseMultilinearExtension(and Sparse) https://github.com/arkworks-rs/algebra/tree/master/poly/src/evaluations/multivariate/multilinear from arkworks into Spartan. This requires moving the specific Spartan functionalities in separate traits.
#[derive(Debug, Clone, Eq, PartialEq, Hash, CanonicalDeserialize, CanonicalSerialize)]
pub struct DensePolynomial<F: PrimeField> {
  pub num_vars: usize, // the number of variables in the multilinear polynomial
  pub len: usize,
  pub Z: Vec<F>, // evaluations of the polynomial in all the 2^num_vars Boolean inputs
}

impl<F: PrimeField> MultilinearExtension<F> for DensePolynomial<F> {
  fn num_vars(&self) -> usize {
    self.get_num_vars()
  }

  fn evaluate(&self, point: &[F]) -> Option<F> {
    if point.len() == self.num_vars {
      Some(self.evaluate(&point))
    } else {
      None
    }
  }

  fn rand<R: rand::Rng>(num_vars: usize, rng: &mut R) -> Self {
    let evals = (0..(1 << num_vars)).map(|_| F::rand(rng)).collect();
    Self {
      num_vars,
      len: 1 << num_vars,
      Z: evals,
    }
  }

  fn relabel(&self, _a: usize, _b: usize, _k: usize) -> Self {
    unimplemented!()
  }

  fn fix_variables(&self, _partial_point: &[F]) -> Self {
    unimplemented!()
  }

  fn to_evaluations(&self) -> Vec<F> {
    self.Z.to_vec()
  }
}

impl<F: PrimeField> Zero for DensePolynomial<F> {
  fn zero() -> Self {
    Self {
      num_vars: 0,
      len: 1,
      Z: vec![F::zero()],
    }
  }

  fn is_zero(&self) -> bool {
    self.num_vars == 0 && self.len == 1 && self.Z[0].is_zero()
  }
}

impl<F: PrimeField> Add for DensePolynomial<F> {
  type Output = DensePolynomial<F>;
  fn add(self, other: Self) -> Self {
    &self + &other
  }
}

// function needed because the result might have a different lifetime than the
// operands
impl<'a, 'b, F: PrimeField> Add<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
  type Output = DensePolynomial<F>;

  fn add(self, other: &'a DensePolynomial<F>) -> Self::Output {
    if other.is_zero() {
      return self.clone();
    }
    if self.is_zero() {
      return other.clone();
    }
    assert_eq!(self.num_vars, other.num_vars);

    let res = self
      .Z
      .iter()
      .zip(other.Z.iter())
      .map(|(a, b)| *a + *b)
      .collect();
    Self::Output {
      num_vars: self.num_vars,
      len: self.len,
      Z: res,
    }
  }
}

impl<F: PrimeField> AddAssign for DensePolynomial<F> {
  fn add_assign(&mut self, other: Self) {
    *self = &*self + &other;
  }
}

impl<'a, 'b, F: PrimeField> AddAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
  fn add_assign(&mut self, other: &'a DensePolynomial<F>) {
    *self = &*self + other;
  }
}

impl<'a, 'b, F: PrimeField> AddAssign<(F, &'a DensePolynomial<F>)> for DensePolynomial<F> {
  fn add_assign(&mut self, (scalar, other): (F, &'a DensePolynomial<F>)) {
    let other = Self {
      num_vars: other.num_vars,
      len: 1 << other.num_vars,
      Z: other.Z.iter().map(|x| scalar * x).collect(),
    };
    *self = &*self + &other;
  }
}

impl<F: PrimeField> Neg for DensePolynomial<F> {
  type Output = DensePolynomial<F>;

  fn neg(self) -> Self::Output {
    Self::Output {
      num_vars: self.num_vars,
      len: self.len,
      Z: self.Z.iter().map(|x| -*x).collect(),
    }
  }
}

impl<F: PrimeField> Sub for DensePolynomial<F> {
  type Output = DensePolynomial<F>;

  fn sub(self, other: Self) -> Self::Output {
    &self - &other
  }
}

impl<'a, 'b, F: PrimeField> Sub<&'a DensePolynomial<F>> for &'b DensePolynomial<F> {
  type Output = DensePolynomial<F>;

  fn sub(self, other: &'a DensePolynomial<F>) -> Self::Output {
    self + &other.clone().neg()
  }
}

impl<F: PrimeField> SubAssign for DensePolynomial<F> {
  fn sub_assign(&mut self, other: Self) {
    *self = &*self - &other;
  }
}

impl<'a, 'b, F: PrimeField> SubAssign<&'a DensePolynomial<F>> for DensePolynomial<F> {
  fn sub_assign(&mut self, other: &'a DensePolynomial<F>) {
    *self = &*self - other;
  }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PolyCommitmentGens<E: Pairing> {
  pub gens: DotProductProofGens<E::G1>,
  pub ck: CommitterKey<E>,
  pub vk: VerifierKey<E>,
}

impl<E: Pairing> PolyCommitmentGens<E> {
  // num vars is the number of variables in the multilinear polynomial
  // this gives the maximum degree bound
  pub fn setup(num_vars: usize, label: &'static [u8]) -> PolyCommitmentGens<E> {
    let (_left, right) = EqPolynomial::<E::ScalarField>::compute_factored_lens(num_vars);
    let gens = DotProductProofGens::new(right.pow2(), label);

    // Generates the SRS and trims it based on the number of variables in the
    // multilinear polynomial.
    let mut rng = rand::thread_rng();
    let pst_gens = MultilinearPC::<E>::setup(num_vars / 2, &mut rng);
    let (ck, vk) = MultilinearPC::<E>::trim(&pst_gens, num_vars / 2);

    PolyCommitmentGens { gens, ck, vk }
  }
}

pub struct PolyCommitmentBlinds<F: PrimeField> {
  blinds: Vec<F>,
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PolyCommitment<G: CurveGroup> {
  C: Vec<G::Affine>,
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ConstPolyCommitment<G: CurveGroup> {
  C: G,
}

pub struct EqPolynomial<S: PrimeField> {
  r: Vec<S>,
}

impl<F: PrimeField> EqPolynomial<F> {
  pub fn new(r: Vec<F>) -> Self {
    EqPolynomial { r }
  }

  pub fn evaluate(&self, rx: &[F]) -> F {
    assert_eq!(self.r.len(), rx.len());
    (0..rx.len())
      .map(|i| self.r[i] * rx[i] + (F::one() - self.r[i]) * (F::one() - rx[i]))
      .product()
  }

  pub fn evals(&self) -> Vec<F> {
    let ell = self.r.len();

    let mut evals: Vec<F> = vec![F::one(); ell.pow2()];
    let mut size = 1;
    for j in 0..ell {
      // in each iteration, we double the size of chis
      size *= 2;
      // TODO: this reverse causes inconsistent evaluation in comparison to the
      //evaluation function in ark-poly-commit, we should look into this to
      // avoid the extra constraints in the circuit
      for i in (0..size).rev().step_by(2) {
        // copy each element from the prior iteration twice
        let scalar = evals[i / 2];
        evals[i] = scalar * self.r[j];
        evals[i - 1] = scalar - evals[i];
      }
    }
    evals
  }

  pub fn compute_factored_lens(ell: usize) -> (usize, usize) {
    (ell / 2, ell - ell / 2)
  }

  pub fn compute_factored_evals(&self) -> (Vec<F>, Vec<F>) {
    let ell = self.r.len();
    let (left_num_vars, _right_num_vars) = EqPolynomial::<F>::compute_factored_lens(ell);

    let L = EqPolynomial::new(self.r[..left_num_vars].to_vec()).evals();
    let R = EqPolynomial::new(self.r[left_num_vars..ell].to_vec()).evals();

    (L, R)
  }
}

pub struct IdentityPolynomial {
  size_point: usize,
}

impl IdentityPolynomial {
  pub fn new(size_point: usize) -> Self {
    IdentityPolynomial { size_point }
  }

  pub fn evaluate<F: PrimeField>(&self, r: &[F]) -> F {
    let len = r.len();
    assert_eq!(len, self.size_point);
    (0..len)
      .map(|i| F::from((len - i - 1).pow2() as u64) * r[i])
      .sum()
  }
}

impl<F: PrimeField> DensePolynomial<F> {
  pub fn new(Z: Vec<F>) -> Self {
    DensePolynomial {
      num_vars: Z.len().log_2(),
      len: Z.len(),
      Z,
    }
  }

  pub fn get_num_vars(&self) -> usize {
    self.num_vars
  }

  pub fn len(&self) -> usize {
    self.len
  }

  pub fn clone(&self) -> Self {
    DensePolynomial::new(self.Z[0..self.len].to_vec())
  }

  pub fn split(&self, idx: usize) -> (Self, Self) {
    assert!(idx < self.len());
    (
      DensePolynomial::new(self.Z[..idx].to_vec()),
      DensePolynomial::new(self.Z[idx..2 * idx].to_vec()),
    )
  }

  #[cfg(feature = "multicore")]
  fn commit_inner<G>(&self, blinds: &[F], gens: &MultiCommitGens<G>) -> PolyCommitment<G>
  where
    G: CurveGroup<ScalarField = F>,
  {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .into_iter()
      .map(|i| {
        let slice = &self.Z[R_size * i..R_size * (i + 1)];
        PedersenCommit::commit_slice(slice, &blinds[i], gens).into_affine()
      })
      .collect();
    PolyCommitment { C }
  }

  #[cfg(not(feature = "multicore"))]
  fn commit_inner<G>(&self, blinds: &[Scalar], gens: &MultiCommitGens) -> PolyCommitment
  where
    G: CurveGroup<Affine = F>,
  {
    let L_size = blinds.len();
    let R_size = self.Z.len() / L_size;
    assert_eq!(L_size * R_size, self.Z.len());
    let C = (0..L_size)
      .map(|i| {
        PedersenCommit::commit_slice(&self.Z[R_size * i..R_size * (i + 1)], &blinds[i], gens)
          .into_affine()
      })
      .collect();
    PolyCommitment { C }
  }

  pub fn commit<E>(
    &self,
    gens: &PolyCommitmentGens<E>,
    random_blinds: bool,
  ) -> (PolyCommitment<E::G1>, PolyCommitmentBlinds<E::ScalarField>)
  where
    E: Pairing<ScalarField = F>,
  {
    let n = self.Z.len();
    let ell = self.get_num_vars();
    assert_eq!(n, ell.pow2());
    let (left_num_vars, right_num_vars) =
      EqPolynomial::<E::ScalarField>::compute_factored_lens(ell);
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    assert_eq!(L_size * R_size, n);

    let blinds = PolyCommitmentBlinds {
      blinds: if random_blinds {
        (0..L_size)
          .map(|_| F::rand(&mut rand::thread_rng()))
          .collect::<Vec<_>>()
      } else {
        (0..L_size).map(|_| F::zero()).collect::<Vec<_>>()
      },
    };

    (self.commit_inner(&blinds.blinds, &gens.gens.gens_n), blinds)
  }

  pub fn bound(&self, L: &[F]) -> Vec<F> {
    let (left_num_vars, right_num_vars) =
      EqPolynomial::<F>::compute_factored_lens(self.get_num_vars());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();
    (0..R_size)
      .map(|i| (0..L_size).map(|j| L[j] * self.Z[j * R_size + i]).sum())
      .collect()
  }

  pub fn bound_poly_var_top(&mut self, r: &F) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[i] + (self.Z[i + n] - self.Z[i]) * r;
    }
    self.num_vars -= 1;
    self.len = n;
  }

  pub fn bound_poly_var_bot(&mut self, r: &F) {
    let n = self.len() / 2;
    for i in 0..n {
      self.Z[i] = self.Z[2 * i] + (self.Z[2 * i + 1] - self.Z[2 * i]) * r;
    }
    self.num_vars -= 1;
    self.len = n;
  }

  // returns Z(r) in O(n) time
  pub fn evaluate(&self, r: &[F]) -> F {
    // r must have a value for each variable
    assert_eq!(r.len(), self.get_num_vars());
    let chis = EqPolynomial::new(r.to_vec()).evals();
    assert_eq!(chis.len(), self.Z.len());
    crate::dot_product(&self.Z, &chis)
  }

  fn vec(&self) -> &Vec<F> {
    &self.Z
  }

  pub fn extend(&mut self, other: &DensePolynomial<F>) {
    // TODO: allow extension even when some vars are bound
    assert_eq!(self.Z.len(), self.len);
    let other_vec = other.vec();
    assert_eq!(other_vec.len(), self.len);
    self.Z.extend(other_vec);
    self.num_vars += 1;
    self.len *= 2;
    assert_eq!(self.Z.len(), self.len);
  }

  pub fn merge<'a, I>(polys: I) -> DensePolynomial<F>
  where
    I: IntoIterator<Item = &'a DensePolynomial<F>>,
  {
    let mut Z: Vec<F> = Vec::new();
    for poly in polys.into_iter() {
      Z.extend(poly.vec());
    }

    // pad the polynomial with zero polynomial at the end
    Z.resize(Z.len().next_power_of_two(), F::zero());

    DensePolynomial::new(Z)
  }

  pub fn from_usize(Z: &[usize]) -> Self {
    DensePolynomial::new(
      (0..Z.len())
        .map(|i| F::from(Z[i] as u64))
        .collect::<Vec<F>>(),
    )
  }
}

impl<F: PrimeField> Index<usize> for DensePolynomial<F> {
  type Output = F;

  #[inline(always)]
  fn index(&self, _index: usize) -> &F {
    &(self.Z[_index])
  }
}

impl<G: CurveGroup> TranscriptWriter<G::ScalarField> for PolyCommitment<G> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<G::ScalarField>) {
    for i in 0..self.C.len() {
      transcript.append_point(b"", &self.C[i].into_group());
    }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PolyEvalProof<E: Pairing> {
  proof: DotProductProofLog<E::G1>,
}

impl<E> PolyEvalProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  pub fn prove(
    poly: &DensePolynomial<E::ScalarField>,
    blinds_opt: Option<&PolyCommitmentBlinds<E::ScalarField>>,
    r: &[E::ScalarField], // point at which the polynomial is evaluated
    Zr: &E::ScalarField,  // evaluation of \widetilde{Z}(r)
    blind_Zr_opt: Option<&E::ScalarField>, // specifies a blind for Zr
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> (PolyEvalProof<E>, E::G1) {
    // transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // assert vectors are of the right size
    assert_eq!(poly.get_num_vars(), r.len());

    let (left_num_vars, right_num_vars) =
      EqPolynomial::<E::ScalarField>::compute_factored_lens(r.len());
    let L_size = left_num_vars.pow2();
    let R_size = right_num_vars.pow2();

    let default_blinds = PolyCommitmentBlinds {
      blinds: vec![E::ScalarField::zero(); L_size],
    };
    let blinds = blinds_opt.map_or(&default_blinds, |p| p);

    assert_eq!(blinds.blinds.len(), L_size);

    let zero = E::ScalarField::zero();
    let blind_Zr = blind_Zr_opt.map_or(&zero, |p| p);

    // compute the L and R vectors
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();
    assert_eq!(L.len(), L_size);
    assert_eq!(R.len(), R_size);

    // compute the vector underneath L*Z and the L*blinds
    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = poly.bound(&L);
    let LZ_blind: E::ScalarField = (0..L.len()).map(|i| blinds.blinds[i] * L[i]).sum();

    // a dot product proof of size R_size
    let (proof, _C_LR, C_Zr_prime) = DotProductProofLog::prove(
      &gens.gens,
      transcript,
      LZ.as_slice(),
      &LZ_blind,
      &R,
      Zr,
      blind_Zr,
    );

    (PolyEvalProof { proof }, C_Zr_prime)
  }

  pub fn verify(
    &self,
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    r: &[E::ScalarField], // point at which the polynomial is evaluated
    C_Zr: &E::G1,         // commitment to \widetilde{Z}(r)
    comm: &PolyCommitment<E::G1>,
  ) -> Result<(), ProofVerifyError> {
    // transcript.append_protocol_name(PolyEvalProof::protocol_name());

    // compute L and R
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    // compute a weighted sum of commitments and L
    // NOTE: This is necessary because of blst not supporting 0 points in msm
    // TODO: fix the polycommit generators not being 0 - this should not have to be
    let (c, s): (Vec<_>, Vec<_>) = comm
      .C
      .iter()
      .zip(L.iter())
      .filter(|(c, _)| !c.is_zero())
      .unzip();
    let C_LZ = <E::G1 as VariableBaseMSM>::msm(&c, &s).expect("msm of different length");

    self
      .proof
      .verify(R.len(), &gens.gens, transcript, &R, &C_LZ, C_Zr)
  }

  pub fn verify_plain(
    &self,
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
    r: &[E::ScalarField], // point at which the polynomial is evaluated
    Zr: &E::ScalarField,  // evaluation \widetilde{Z}(r)
    comm: &PolyCommitment<E::G1>,
  ) -> Result<(), ProofVerifyError> {
    // compute a commitment to Zr with a blind of zero
    let C_Zr = PedersenCommit::commit_scalar(Zr, &E::ScalarField::zero(), &gens.gens.gens_1);

    self.verify(gens, transcript, r, &C_Zr, comm)
  }
}

#[cfg(test)]
mod tests {
  use crate::ark_std::One;
  use crate::parameters::poseidon_params;

  use super::*;
  use ark_std::UniformRand;

  type F = ark_bls12_377::Fr;
  type E = ark_bls12_377::Bls12_377;

  fn evaluate_with_LR(Z: &[F], r: &[F]) -> F {
    let eq = EqPolynomial::new(r.to_vec());
    let (L, R) = eq.compute_factored_evals();

    let ell = r.len();
    // ensure ell is even
    assert!(ell % 2 == 0);
    // compute n = 2^\ell
    let n = ell.pow2();
    // compute m = sqrt(n) = 2^{\ell/2}
    let m = n.square_root();

    // compute vector-matrix product between L and Z viewed as a matrix
    let LZ = (0..m)
      .map(|i| (0..m).map(|j| L[j] * Z[j * m + i]).sum())
      .collect::<Vec<F>>();

    // compute dot product between LZ and R
    crate::dot_product(&LZ, &R)
  }

  #[test]
  fn check_polynomial_evaluation() {
    // Z = [1, 2, 1, 4]
    let Z = vec![F::one(), F::from(2), F::from(1), F::from(4)];

    // r = [4,3]
    let r = vec![F::from(4), F::from(3)];

    let eval_with_LR = evaluate_with_LR(&Z, &r);
    let poly = DensePolynomial::new(Z);

    let eval = poly.evaluate(&r);
    assert_eq!(eval, F::from(28));
    assert_eq!(eval_with_LR, eval);
  }

  pub fn compute_factored_chis_at_r(r: &[F]) -> (Vec<F>, Vec<F>) {
    let mut L: Vec<F> = Vec::new();
    let mut R: Vec<F> = Vec::new();

    let ell = r.len();
    assert!(ell % 2 == 0); // ensure ell is even
    let n = ell.pow2();
    let m = n.square_root();

    // compute row vector L
    for i in 0..m {
      let mut chi_i = F::one();
      for j in 0..ell / 2 {
        let bit_j = ((m * i) & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= F::one() - r[j];
        }
      }
      L.push(chi_i);
    }

    // compute column vector R
    for i in 0..m {
      let mut chi_i = F::one();
      for j in ell / 2..ell {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= F::one() - r[j];
        }
      }
      R.push(chi_i);
    }
    (L, R)
  }

  pub fn compute_chis_at_r(r: &[F]) -> Vec<F> {
    let ell = r.len();
    let n = ell.pow2();
    let mut chis: Vec<F> = Vec::new();
    for i in 0..n {
      let mut chi_i = F::one();
      for j in 0..r.len() {
        let bit_j = (i & (1 << (r.len() - j - 1))) > 0;
        if bit_j {
          chi_i *= r[j];
        } else {
          chi_i *= F::one() - r[j];
        }
      }
      chis.push(chi_i);
    }
    chis
  }

  pub fn compute_outerproduct(L: Vec<F>, R: Vec<F>) -> Vec<F> {
    assert_eq!(L.len(), R.len());
    (0..L.len())
      .map(|i| (0..R.len()).map(|j| L[i] * R[j]).collect::<Vec<F>>())
      .collect::<Vec<Vec<F>>>()
      .into_iter()
      .flatten()
      .collect::<Vec<F>>()
  }

  #[test]
  fn check_memoized_chis() {
    let mut rng = ark_std::rand::thread_rng();

    let s = 10;
    let mut r: Vec<F> = Vec::new();
    for _i in 0..s {
      r.push(F::rand(&mut rng));
    }
    let chis = tests::compute_chis_at_r(&r);
    let chis_m = EqPolynomial::new(r).evals();
    assert_eq!(chis, chis_m);
  }

  #[test]
  fn check_factored_chis() {
    let mut rng = ark_std::rand::thread_rng();

    let s = 10;
    let mut r: Vec<F> = Vec::new();
    for _i in 0..s {
      r.push(F::rand(&mut rng));
    }
    let chis = EqPolynomial::new(r.clone()).evals();
    let (L, R) = EqPolynomial::new(r).compute_factored_evals();
    let O = compute_outerproduct(L, R);
    assert_eq!(chis, O);
  }

  #[test]
  fn check_memoized_factored_chis() {
    let mut rng = ark_std::rand::thread_rng();

    let s = 10;
    let mut r: Vec<F> = Vec::new();
    for _i in 0..s {
      r.push(F::rand(&mut rng));
    }
    let (L, R) = tests::compute_factored_chis_at_r(&r);
    let eq = EqPolynomial::new(r);
    let (L2, R2) = eq.compute_factored_evals();
    assert_eq!(L, L2);
    assert_eq!(R, R2);
  }

  #[test]
  fn check_polynomial_commit() {
    let Z = vec![F::from(1), F::from(2), F::from(1), F::from(4)];
    let poly = DensePolynomial::new(Z);

    // r = [4,3]
    let r = vec![F::from(4), F::from(3)];
    let eval = poly.evaluate(&r);
    assert_eq!(eval, F::from(28));

    let gens = PolyCommitmentGens::setup(poly.get_num_vars(), b"test-two");
    let (poly_commitment, blinds) = poly.commit(&gens, false);

    let params = poseidon_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let (proof, C_Zr) = PolyEvalProof::<E>::prove(
      &poly,
      Some(&blinds),
      &r,
      &eval,
      None,
      &gens,
      &mut prover_transcript,
    );

    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(&gens, &mut verifier_transcript, &r, &C_Zr, &poly_commitment)
      .is_ok());
  }
}
