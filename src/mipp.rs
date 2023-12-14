use crate::poseidon_transcript::PoseidonTranscript;
use crate::transcript::Transcript;
use ark_ec::scalar_mul::variable_base::VariableBaseMSM;
use ark_ec::CurveGroup;
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use ark_poly_commit::multilinear_pc::data_structures::{
  CommitmentG2, CommitterKey, ProofG1, VerifierKey,
};
use ark_poly_commit::multilinear_pc::MultilinearPC;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::One;
use ark_std::Zero;
use rayon::iter::ParallelIterator;
use rayon::prelude::IntoParallelIterator;
use rayon::prelude::*;
use std::ops::{AddAssign, Mul, MulAssign};
use thiserror::Error;

#[derive(Debug, Clone, CanonicalDeserialize, CanonicalSerialize)]
pub struct MippProof<E: Pairing> {
  pub comms_t: Vec<(<E as Pairing>::TargetField, <E as Pairing>::TargetField)>,
  pub comms_u: Vec<(E::G1Affine, E::G1Affine)>,
  pub final_a: E::G1Affine,
  pub final_h: E::G2Affine,
  pub pst_proof_h: ProofG1<E>,
}

impl<E: Pairing> MippProof<E> {
  pub fn prove(
    transcript: &mut PoseidonTranscript<E::BaseField>,
    ck: &CommitterKey<E>,
    a: Vec<E::G1Affine>,
    y: Vec<E::ScalarField>,
    h: Vec<E::G2Affine>,
    U: &E::G1Affine,
    _T: &<E as Pairing>::TargetField,
  ) -> Result<MippProof<E>, Error> {
    // the values of vectors A and y rescaled at each step of the loop
    let (mut m_a, mut m_y) = (a.clone(), y.clone());
    // the values of the commitment keys h for the vector A rescaled at
    //  each step of the loop
    let mut m_h = h.clone();

    // storing the cross commitments for including in the proofs
    let mut comms_t = Vec::new();
    let mut comms_u = Vec::new();

    // the transcript challenges
    let mut xs: Vec<E::ScalarField> = Vec::new();
    let mut xs_inv: Vec<E::ScalarField> = Vec::new();

    // we append only the MIPP because the aggregated commitment T has been
    // appended already
    transcript.append(b"U", U);

    while m_a.len() > 1 {
      // recursive step
      // Recurse with problem of half size
      let split = m_a.len() / 2;

      // MIPP where n' = split///
      // a[:n']   a[n':]
      let (a_l, a_r) = m_a.split_at_mut(split);
      // y[:n']   y[n':]
      let (y_l, y_r) = m_y.split_at_mut(split);
      // h[:n']   y[n':]
      let (h_l, h_r) = m_h.split_at_mut(split);

      // since we do this in parallel we take reference first so it can be
      // moved within the macro's rayon scope.
      let (_rh_l, _rh_r) = (&h_l, &h_r);
      let (ra_l, ra_r) = (&a_l, &a_r);
      let (ry_l, ry_r) = (&y_l, &y_r);

      try_par! {
       // MIPP part
       // Compute cross commitments
       // u_l = a[n':] ^ y[:n']
       // TODO to replace by bitsf_multiexp
       let comm_u_l = multiexponentiation(ra_l, &ry_r),
       // u_r = a[:n'] ^ y[n':]
       let comm_u_r = multiexponentiation(ra_r, &ry_l)
      };

      par! {
        // Compute the cross pairing products over the distinct halfs of A
        // t_l = a[n':] * h[:n']
        let comm_t_l = pairings_product::<E>(&a_l, h_r),
        // t_r = a[:n'] * h[n':]
        let comm_t_r = pairings_product::<E>(&a_r, h_l)

      };

      // Fiat-Shamir challenge
      transcript.append(b"comm_u_l", &comm_u_l);
      transcript.append(b"comm_u_r", &comm_u_r);
      transcript.append(b"comm_t_l", &comm_t_l);
      transcript.append(b"comm_t_r", &comm_t_r);
      let c_inv = transcript.challenge_scalar::<E::ScalarField>(b"challenge_i");

      // Optimization for multiexponentiation to rescale G2 elements with
      // 128-bit challenge Swap 'c' and 'c_inv' since we
      // can't control bit size of c_inv
      let c = c_inv.inverse().unwrap();

      // Set up values for next step of recursion by compressing as follows
      // a[n':] + a[:n']^x
      compress(&mut m_a, split, &c);
      // y[n':] + y[:n']^x_inv
      compress_field(&mut m_y, split, &c_inv);
      // h[n':] + h[:n']^x_inv
      compress(&mut m_h, split, &c_inv);

      comms_t.push((comm_t_l, comm_t_r));
      comms_u.push((comm_u_l.into_affine(), comm_u_r.into_affine()));
      xs.push(c);
      xs_inv.push(c_inv);
    }
    assert!(m_a.len() == 1 && m_y.len() == 1 && m_h.len() == 1);

    let final_a = m_a[0];
    let final_h = m_h[0];

    // get the structured polynomial p_h for which final_h = h^p_h(vec{t})
    // is the PST commitment given generator h and toxic waste \vec{t}
    let poly = DenseMultilinearExtension::<E::ScalarField>::from_evaluations_vec(
      xs_inv.len(),
      Self::polynomial_evaluations_from_transcript::<E::ScalarField>(&xs_inv),
    );

    let c = MultilinearPC::<E>::commit_g2(ck, &poly);
    debug_assert!(c.h_product == final_h);

    // generate a proof of opening final_h at the random point rs
    // from the transcript
    let rs: Vec<E::ScalarField> = (0..poly.num_vars)
      .into_iter()
      .map(|_| transcript.challenge_scalar::<E::ScalarField>(b"random_point"))
      .collect();

    let pst_proof_h = MultilinearPC::<E>::open_g1(ck, &poly, &rs);

    Ok(MippProof {
      comms_t,
      comms_u,
      final_a,
      final_h,
      pst_proof_h,
    })
  }

  // builds the polynomial p_h in Lagrange basis which uses the
  // inverses of transcript challenges this is the following
  // structured polynomial $\prod_i(1 - z_i + cs_inv[m - i  - 1] * z_i)$
  // where m is the length of cs_inv and z_i is the unknown
  fn polynomial_evaluations_from_transcript<F: Field>(cs_inv: &[F]) -> Vec<F> {
    let m = cs_inv.len();
    let pow_m = 2_usize.pow(m as u32);

    // constructs the list of evaluations over the boolean hypercube \{0,1\}^m
    let evals = (0..pow_m)
      .into_par_iter()
      .map(|i| {
        let mut res = F::one();
        for j in 0..m {
          // we iterate from lsb to msb and, in case the bit is 1,
          // we multiply by the corresponding challenge i.e whose
          // index corresponds to the bit's position
          if (i >> j) & 1 == 1 {
            res *= cs_inv[m - j - 1];
          }
        }
        res
      })
      .collect();
    evals
  }

  pub fn verify(
    vk: &VerifierKey<E>,
    transcript: &mut PoseidonTranscript<E::BaseField>,
    proof: &MippProof<E>,
    point: Vec<E::ScalarField>,
    U: &E::G1Affine,
    T: &<E as Pairing>::TargetField,
  ) -> bool {
    let comms_u = proof.comms_u.clone();
    let comms_t = proof.comms_t.clone();

    let mut xs = Vec::new();
    let mut xs_inv = Vec::new();
    let mut final_y = E::ScalarField::one();

    let mut final_res = MippTU {
      tc: T.clone(),
      uc: U.into_group(),
    };

    transcript.append(b"U", U);

    // Challenges need to be generated first in sequential order so the
    // prover and the verifier have a consistent view of the transcript
    for (i, (comm_u, comm_t)) in comms_u.iter().zip(comms_t.iter()).enumerate() {
      let (comm_u_l, comm_u_r) = comm_u;
      let (comm_t_l, comm_t_r) = comm_t;

      // Fiat-Shamir challenge
      transcript.append(b"comm_u_l", comm_u_l);
      transcript.append(b"comm_u_r", comm_u_r);
      transcript.append(b"comm_t_l", comm_t_l);
      transcript.append(b"comm_t_r", comm_t_r);
      let c_inv = transcript.challenge_scalar::<E::ScalarField>(b"challenge_i");
      let c = c_inv.inverse().unwrap();

      xs.push(c);
      xs_inv.push(c_inv);

      // the verifier computes the final_y by themselves because
      // this is field operations so it's quite fast and parallelisation
      // doesn't bring much improvement
      final_y *= E::ScalarField::one() + c_inv.mul(point[i]) - point[i];
    }

    // First, each entry of T and U are multiplied independently by their
    // respective challenges which is done in parralel and, at the end,
    // the results are merged together for each vector following their
    // corresponding merge operation.
    enum Op<'a, E: Pairing> {
      TC(&'a E::TargetField, <E::ScalarField as PrimeField>::BigInt),
      UC(&'a E::G1Affine, &'a E::ScalarField),
    }

    let res = comms_t
      .par_iter()
      .zip(comms_u.par_iter())
      .zip(xs.par_iter().zip(xs_inv.par_iter()))
      .flat_map(|((comm_t, comm_u), (c, c_inv))| {
        let (comm_t_l, comm_t_r) = comm_t;
        let (comm_u_l, comm_u_r) = comm_u;

        // we multiple left side by x^-1 and right side by x
        vec![
          Op::TC::<E>(comm_t_l, c_inv.into_bigint()),
          Op::TC(comm_t_r, c.into_bigint()),
          Op::UC(comm_u_l, c_inv),
          Op::UC(comm_u_r, c),
        ]
      })
      .fold(MippTU::<E>::default, |mut res, op: Op<E>| {
        match op {
          Op::TC(tx, c) => {
            let tx: E::TargetField = tx.pow(c);
            res.tc.mul_assign(&tx);
          }
          Op::UC(zx, c) => {
            let uxp: E::G1 = zx.mul(c);
            res.uc.add_assign(&uxp);
          }
        }
        res
      })
      .reduce(MippTU::default, |mut acc_res, res| {
        acc_res.merge(&res);
        acc_res
      });

    // the initial values of T and U are also merged to get the final result
    let ref_final_res = &mut final_res;
    ref_final_res.merge(&res);

    // get the point rs from the transcript, used by the prover to generate
    // the PST proof
    let mut rs: Vec<E::ScalarField> = Vec::new();
    let m = xs_inv.len();
    for _i in 0..m {
      let r = transcript.challenge_scalar::<E::ScalarField>(b"random_point");
      rs.push(r);
    }
    // Given p_h is structured as defined above, the verifier can compute
    // p_h(rs) by themselves in O(m) time
    let v = (0..m)
      .into_par_iter()
      .map(|i| E::ScalarField::one() + rs[i].mul(xs_inv[m - i - 1]) - rs[i])
      .product();

    let comm_h = CommitmentG2 {
      nv: m,
      h_product: proof.final_h,
    };

    // final_h is the commitment of p_h so the verifier can perform
    // a PST verification at the random point rs, given the pst proof
    // received from the prover prover
    let check_h = MultilinearPC::<E>::check_2(vk, &comm_h, &rs, v, &proof.pst_proof_h);
    assert!(check_h == true);

    let final_u = proof.final_a.mul(final_y);
    let final_t: <E as Pairing>::TargetField = E::pairing(proof.final_a, proof.final_h).0;

    let check_t = ref_final_res.tc == final_t;
    assert!(check_t == true);

    let check_u = ref_final_res.uc == final_u;
    assert!(check_u == true);
    check_h & check_u
  }
}

/// MippTU keeps track of the variables that have been sent by the prover and
/// must be multiplied together by the verifier.
struct MippTU<E: Pairing> {
  pub tc: E::TargetField,
  pub uc: E::G1,
}

impl<E> Default for MippTU<E>
where
  E: Pairing,
{
  fn default() -> Self {
    Self {
      tc: E::TargetField::one(),
      uc: E::G1::zero(),
    }
  }
}

impl<E> MippTU<E>
where
  E: Pairing,
{
  fn merge(&mut self, other: &Self) {
    self.tc.mul_assign(&other.tc);
    self.uc.add_assign(&other.uc);
  }
}

/// compress modifies the `vec` vector by setting the value at
/// index $i:0 -> split$  $vec[i] = vec[i] + vec[i+split]^scaler$.
/// The `vec` vector is half of its size after this call.
pub fn compress<C: AffineRepr>(vec: &mut Vec<C>, split: usize, scaler: &C::ScalarField) {
  let (left, right) = vec.split_at_mut(split);
  left
    .par_iter_mut()
    .zip(right.par_iter())
    .for_each(|(a_l, a_r)| {
      // TODO remove that with master version
      let mut x = a_r.mul(scaler);
      x.add_assign(a_l.into_group());
      *a_l = x.into_affine();
    });
  let len = left.len();
  vec.resize(len, C::zero());
}

// TODO make that generic with points as well
pub fn compress_field<F: PrimeField>(vec: &mut Vec<F>, split: usize, scaler: &F) {
  let (left, right) = vec.split_at_mut(split);
  assert!(left.len() == right.len());
  left
    .par_iter_mut()
    .zip(right.par_iter_mut())
    .for_each(|(a_l, a_r)| {
      // TODO remove copy
      a_r.mul_assign(scaler);
      a_l.add_assign(a_r.clone());
    });
  let len = left.len();
  vec.resize(len, F::zero());
}

pub fn multiexponentiation<G: AffineRepr>(
  left: &[G],
  right: &[G::ScalarField],
) -> Result<G::Group, Error> {
  if left.len() != right.len() {
    return Err(Error::InvalidIPVectorLength);
  }

  Ok(<G::Group as VariableBaseMSM>::msm_unchecked(left, right))
}

pub fn pairings_product<E: Pairing>(gs: &[E::G1Affine], hs: &[E::G2Affine]) -> E::TargetField {
  E::multi_pairing(gs, hs).0
}

#[derive(Debug, Error)]
pub enum Error {
  #[error("Serialization error: {0}")]
  Serialization(#[from] SerializationError),

  #[error("Vectors length do not match for inner product (IP)")]
  InvalidIPVectorLength,
  // #[error("Commitment key length invalid")]
  // InvalidKeyLength,

  // #[error("Invalid pairing result")]
  // InvalidPairing,

  // #[error("Invalid SRS: {0}")]
  // InvalidSRS(String),

  // #[error("Invalid proof: {0}")]
  // InvalidProof(String),

  // #[error("Malformed Groth16 verifying key")]
  // MalformedVerifyingKey,
}
