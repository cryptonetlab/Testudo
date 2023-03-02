#![allow(clippy::type_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::needless_range_loop)]
use super::dense_mlpoly::DensePolynomial;
use super::dense_mlpoly::{
  EqPolynomial, IdentityPolynomial, PolyCommitment, PolyCommitmentGens, PolyEvalProof,
};
use super::errors::ProofVerifyError;
use super::math::Math;
use super::product_tree::{DotProductCircuit, ProductCircuit, ProductCircuitEvalProofBatched};
use super::timer::Timer;
use crate::poseidon_transcript::{PoseidonTranscript, TranscriptWriter};
use crate::transcript::Transcript;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_ff::{Field, One, Zero};
use ark_serialize::*;
use core::cmp::Ordering;

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct SparseMatEntry<F: PrimeField> {
  row: usize,
  col: usize,
  val: F,
}

impl<F: PrimeField> SparseMatEntry<F> {
  pub fn new(row: usize, col: usize, val: F) -> Self {
    SparseMatEntry { row, col, val }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize, Clone)]
pub struct SparseMatPolynomial<F: PrimeField> {
  num_vars_x: usize,
  num_vars_y: usize,
  M: Vec<SparseMatEntry<F>>,
}

pub struct Derefs<F: PrimeField> {
  row_ops_val: Vec<DensePolynomial<F>>,
  col_ops_val: Vec<DensePolynomial<F>>,
  comb: DensePolynomial<F>,
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DerefsCommitment<G: CurveGroup> {
  comm_ops_val: PolyCommitment<G>,
}

impl<F: PrimeField> Derefs<F> {
  pub fn new(row_ops_val: Vec<DensePolynomial<F>>, col_ops_val: Vec<DensePolynomial<F>>) -> Self {
    assert_eq!(row_ops_val.len(), col_ops_val.len());

    let derefs = {
      // combine all polynomials into a single polynomial (used below to produce a single commitment)
      let comb = DensePolynomial::merge(row_ops_val.iter().chain(col_ops_val.iter()));

      Derefs {
        row_ops_val,
        col_ops_val,
        comb,
      }
    };

    derefs
  }

  pub fn commit<E>(&self, gens: &PolyCommitmentGens<E>) -> DerefsCommitment<E::G1>
  where
    E: Pairing<ScalarField = F>,
  {
    let (comm_ops_val, _blinds) = self.comb.commit(gens, false);
    DerefsCommitment { comm_ops_val }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DerefsEvalProof<E: Pairing> {
  proof_derefs: PolyEvalProof<E>,
}

impl<E> DerefsEvalProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  fn prove_single(
    joint_poly: &DensePolynomial<E::ScalarField>,
    r: &[E::ScalarField],
    evals: Vec<E::ScalarField>,
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> PolyEvalProof<E> {
    assert_eq!(joint_poly.get_num_vars(), r.len() + evals.len().log_2());

    // append the claimed evaluations to transcript
    // evals.append_to_transcript(b"evals_ops_val", transcript);
    transcript.append_scalar_vector(b"", &evals);

    // n-to-1 reduction
    let (r_joint, eval_joint) = {
      let challenges = transcript.challenge_scalar_vec(b"", evals.len().log_2());
      let mut poly_evals = DensePolynomial::new(evals);
      for i in (0..challenges.len()).rev() {
        poly_evals.bound_poly_var_bot(&challenges[i]);
      }
      assert_eq!(poly_evals.len(), 1);
      let joint_claim_eval = poly_evals[0];
      let mut r_joint = challenges;
      r_joint.extend(r);

      debug_assert_eq!(joint_poly.evaluate(&r_joint), joint_claim_eval);
      (r_joint, joint_claim_eval)
    };
    // decommit the joint polynomial at r_joint
    transcript.append_scalar(b"", &eval_joint);
    let (proof_derefs, _comm_derefs_eval) = PolyEvalProof::prove(
      joint_poly,
      None,
      &r_joint,
      &eval_joint,
      None,
      gens,
      transcript,
    );

    proof_derefs
  }

  // evalues both polynomials at r and produces a joint proof of opening
  pub fn prove(
    derefs: &Derefs<E::ScalarField>,
    eval_row_ops_val_vec: &[E::ScalarField],
    eval_col_ops_val_vec: &[E::ScalarField],
    r: &[E::ScalarField],
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Self {
    // transcript.append_protocol_name(DerefsEvalProof::protocol_name());

    let evals = {
      let mut evals = eval_row_ops_val_vec.to_owned();
      evals.extend(eval_col_ops_val_vec);
      evals.resize(evals.len().next_power_of_two(), E::ScalarField::zero());
      evals
    };
    let proof_derefs = DerefsEvalProof::prove_single(&derefs.comb, r, evals, gens, transcript);

    DerefsEvalProof { proof_derefs }
  }

  fn verify_single(
    proof: &PolyEvalProof<E>,
    comm: &PolyCommitment<E::G1>,
    r: &[E::ScalarField],
    evals: Vec<E::ScalarField>,
    gens: &PolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Result<(), ProofVerifyError> {
    // append the claimed evaluations to transcript
    // evals.append_to_transcript(b"evals_ops_val", transcript);
    transcript.append_scalar_vector(b"", &evals);

    // n-to-1 reduction
    let challenges = transcript.challenge_scalar_vec(b"", evals.len().log_2());
    let mut poly_evals = DensePolynomial::new(evals);
    for i in (0..challenges.len()).rev() {
      poly_evals.bound_poly_var_bot(&challenges[i]);
    }
    assert_eq!(poly_evals.len(), 1);
    let joint_claim_eval = poly_evals[0];
    let mut r_joint = challenges;
    r_joint.extend(r);

    // decommit the joint polynomial at r_joint
    // joint_claim_eval.append_to_transcript(b"joint_claim_eval", transcript);
    transcript.append_scalar(b"", &joint_claim_eval);

    proof.verify_plain(gens, transcript, &r_joint, &joint_claim_eval, comm)
  }

  // verify evaluations of both polynomials at r
  pub fn verify(
    &self,
    r: &[E::ScalarField],
    eval_row_ops_val_vec: &[E::ScalarField],
    eval_col_ops_val_vec: &[E::ScalarField],
    gens: &PolyCommitmentGens<E>,
    comm: &DerefsCommitment<E::G1>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Result<(), ProofVerifyError> {
    // transcript.append_protocol_name(DerefsEvalProof::protocol_name());
    let mut evals = eval_row_ops_val_vec.to_owned();
    evals.extend(eval_col_ops_val_vec);
    evals.resize(evals.len().next_power_of_two(), E::ScalarField::zero());

    DerefsEvalProof::verify_single(
      &self.proof_derefs,
      &comm.comm_ops_val,
      r,
      evals,
      gens,
      transcript,
    )
  }
}

impl<G: CurveGroup> TranscriptWriter<G::ScalarField> for DerefsCommitment<G> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<G::ScalarField>) {
    self.comm_ops_val.write_to_transcript(transcript);
  }
}
struct AddrTimestamps<F: PrimeField> {
  ops_addr_usize: Vec<Vec<usize>>,
  ops_addr: Vec<DensePolynomial<F>>,
  read_ts: Vec<DensePolynomial<F>>,
  audit_ts: DensePolynomial<F>,
}

impl<F: PrimeField> AddrTimestamps<F> {
  pub fn new(num_cells: usize, num_ops: usize, ops_addr: Vec<Vec<usize>>) -> Self {
    for item in ops_addr.iter() {
      assert_eq!(item.len(), num_ops);
    }

    let mut audit_ts = vec![0usize; num_cells];
    let mut ops_addr_vec: Vec<DensePolynomial<F>> = Vec::new();
    let mut read_ts_vec: Vec<DensePolynomial<F>> = Vec::new();
    for ops_addr_inst in ops_addr.iter() {
      let mut read_ts = vec![0usize; num_ops];

      // since read timestamps are trustworthy, we can simply increment the r-ts to obtain a w-ts
      // this is sufficient to ensure that the write-set, consisting of (addr, val, ts) tuples, is a set
      for i in 0..num_ops {
        let addr = ops_addr_inst[i];
        assert!(addr < num_cells);
        let r_ts = audit_ts[addr];
        read_ts[i] = r_ts;

        let w_ts = r_ts + 1;
        audit_ts[addr] = w_ts;
      }

      ops_addr_vec.push(DensePolynomial::from_usize(ops_addr_inst));
      read_ts_vec.push(DensePolynomial::from_usize(&read_ts));
    }

    AddrTimestamps {
      ops_addr: ops_addr_vec,
      ops_addr_usize: ops_addr,
      read_ts: read_ts_vec,
      audit_ts: DensePolynomial::from_usize(&audit_ts),
    }
  }

  fn deref_mem(addr: &[usize], mem_val: &[F]) -> DensePolynomial<F> {
    DensePolynomial::new(
      (0..addr.len())
        .map(|i| {
          let a = addr[i];
          mem_val[a]
        })
        .collect::<Vec<F>>(),
    )
  }

  pub fn deref(&self, mem_val: &[F]) -> Vec<DensePolynomial<F>> {
    (0..self.ops_addr.len())
      .map(|i| AddrTimestamps::deref_mem(&self.ops_addr_usize[i], mem_val))
      .collect::<Vec<DensePolynomial<F>>>()
  }
}

pub struct MultiSparseMatPolynomialAsDense<F: PrimeField> {
  batch_size: usize,
  val: Vec<DensePolynomial<F>>,
  row: AddrTimestamps<F>,
  col: AddrTimestamps<F>,
  comb_ops: DensePolynomial<F>,
  comb_mem: DensePolynomial<F>,
}

#[derive(CanonicalSerialize, CanonicalDeserialize, Debug)]
pub struct SparseMatPolyCommitmentGens<E: Pairing> {
  gens_ops: PolyCommitmentGens<E>,
  gens_mem: PolyCommitmentGens<E>,
  gens_derefs: PolyCommitmentGens<E>,
}

impl<E: Pairing> SparseMatPolyCommitmentGens<E> {
  pub fn setup(
    label: &'static [u8],
    num_vars_x: usize,
    num_vars_y: usize,
    num_nz_entries: usize,
    batch_size: usize,
  ) -> Self {
    let num_vars_ops =
      num_nz_entries.next_power_of_two().log_2() + (batch_size * 5).next_power_of_two().log_2();
    let num_vars_mem = if num_vars_x > num_vars_y {
      num_vars_x
    } else {
      num_vars_y
    } + 1;
    let num_vars_derefs =
      num_nz_entries.next_power_of_two().log_2() + (batch_size * 2).next_power_of_two().log_2();

    let gens_ops = PolyCommitmentGens::setup(num_vars_ops, label);
    let gens_mem = PolyCommitmentGens::setup(num_vars_mem, label);
    let gens_derefs = PolyCommitmentGens::setup(num_vars_derefs, label);
    SparseMatPolyCommitmentGens {
      gens_ops,
      gens_mem,
      gens_derefs,
    }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SparseMatPolyCommitment<G: CurveGroup> {
  batch_size: usize,
  num_ops: usize,
  num_mem_cells: usize,
  comm_comb_ops: PolyCommitment<G>,
  comm_comb_mem: PolyCommitment<G>,
}

impl<G: CurveGroup> TranscriptWriter<G::ScalarField> for SparseMatPolyCommitment<G> {
  fn write_to_transcript(&self, transcript: &mut PoseidonTranscript<G::ScalarField>) {
    transcript.append_u64(b"", self.batch_size as u64);
    transcript.append_u64(b"", self.num_ops as u64);
    transcript.append_u64(b"", self.num_mem_cells as u64);
    self.comm_comb_ops.write_to_transcript(transcript);
    self.comm_comb_mem.write_to_transcript(transcript);
  }
}

impl<F: PrimeField> SparseMatPolynomial<F> {
  pub fn new(num_vars_x: usize, num_vars_y: usize, M: Vec<SparseMatEntry<F>>) -> Self {
    SparseMatPolynomial {
      num_vars_x,
      num_vars_y,
      M,
    }
  }

  pub fn get_num_nz_entries(&self) -> usize {
    self.M.len().next_power_of_two()
  }

  fn sparse_to_dense_vecs(&self, N: usize) -> (Vec<usize>, Vec<usize>, Vec<F>) {
    assert!(N >= self.get_num_nz_entries());
    let mut ops_row: Vec<usize> = vec![0; N];
    let mut ops_col: Vec<usize> = vec![0; N];
    let mut val: Vec<F> = vec![F::zero(); N];

    for i in 0..self.M.len() {
      ops_row[i] = self.M[i].row;
      ops_col[i] = self.M[i].col;
      val[i] = self.M[i].val;
    }
    (ops_row, ops_col, val)
  }

  fn multi_sparse_to_dense_rep(
    sparse_polys: &[&SparseMatPolynomial<F>],
  ) -> MultiSparseMatPolynomialAsDense<F> {
    assert!(!sparse_polys.is_empty());
    for i in 1..sparse_polys.len() {
      assert_eq!(sparse_polys[i].num_vars_x, sparse_polys[0].num_vars_x);
      assert_eq!(sparse_polys[i].num_vars_y, sparse_polys[0].num_vars_y);
    }

    let N = (0..sparse_polys.len())
      .map(|i| sparse_polys[i].get_num_nz_entries())
      .max()
      .unwrap()
      .next_power_of_two();

    let mut ops_row_vec: Vec<Vec<usize>> = Vec::new();
    let mut ops_col_vec: Vec<Vec<usize>> = Vec::new();
    let mut val_vec: Vec<DensePolynomial<F>> = Vec::new();
    for poly in sparse_polys {
      let (ops_row, ops_col, val) = poly.sparse_to_dense_vecs(N);
      ops_row_vec.push(ops_row);
      ops_col_vec.push(ops_col);
      val_vec.push(DensePolynomial::new(val));
    }

    let any_poly = &sparse_polys[0];

    let num_mem_cells = if any_poly.num_vars_x > any_poly.num_vars_y {
      any_poly.num_vars_x.pow2()
    } else {
      any_poly.num_vars_y.pow2()
    };

    let row = AddrTimestamps::new(num_mem_cells, N, ops_row_vec);
    let col = AddrTimestamps::new(num_mem_cells, N, ops_col_vec);

    // combine polynomials into a single polynomial for commitment purposes
    let comb_ops = DensePolynomial::merge(
      row
        .ops_addr
        .iter()
        .chain(row.read_ts.iter())
        .chain(col.ops_addr.iter())
        .chain(col.read_ts.iter())
        .chain(val_vec.iter()),
    );
    let mut comb_mem = row.audit_ts.clone();
    comb_mem.extend(&col.audit_ts);

    MultiSparseMatPolynomialAsDense {
      batch_size: sparse_polys.len(),
      row,
      col,
      val: val_vec,
      comb_ops,
      comb_mem,
    }
  }

  fn evaluate_with_tables(&self, eval_table_rx: &[F], eval_table_ry: &[F]) -> F {
    assert_eq!(self.num_vars_x.pow2(), eval_table_rx.len());
    assert_eq!(self.num_vars_y.pow2(), eval_table_ry.len());

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        eval_table_rx[row] * eval_table_ry[col] * val
      })
      .sum()
  }

  pub fn multi_evaluate(polys: &[&SparseMatPolynomial<F>], rx: &[F], ry: &[F]) -> Vec<F> {
    let eval_table_rx = EqPolynomial::new(rx.to_vec()).evals();
    let eval_table_ry = EqPolynomial::new(ry.to_vec()).evals();

    (0..polys.len())
      .map(|i| polys[i].evaluate_with_tables(&eval_table_rx, &eval_table_ry))
      .collect::<Vec<F>>()
  }

  pub fn multiply_vec(&self, num_rows: usize, num_cols: usize, z: &[F]) -> Vec<F> {
    assert_eq!(z.len(), num_cols);

    (0..self.M.len())
      .map(|i| {
        let row = self.M[i].row;
        let col = self.M[i].col;
        let val = &self.M[i].val;
        (row, z[col] * val)
      })
      .fold(vec![F::zero(); num_rows], |mut Mz, (r, v)| {
        Mz[r] += v;
        Mz
      })
  }

  pub fn compute_eval_table_sparse(&self, rx: &[F], num_rows: usize, num_cols: usize) -> Vec<F> {
    assert_eq!(rx.len(), num_rows);

    let mut M_evals: Vec<F> = vec![F::zero(); num_cols];

    for i in 0..self.M.len() {
      let entry = &self.M[i];
      M_evals[entry.col] += rx[entry.row] * entry.val;
    }
    M_evals
  }

  pub fn multi_commit<E>(
    sparse_polys: &[&SparseMatPolynomial<F>],
    gens: &SparseMatPolyCommitmentGens<E>,
  ) -> (
    SparseMatPolyCommitment<E::G1>,
    MultiSparseMatPolynomialAsDense<F>,
  )
  where
    E: Pairing<ScalarField = F>,
  {
    let batch_size = sparse_polys.len();
    let dense = SparseMatPolynomial::multi_sparse_to_dense_rep(sparse_polys);

    let (comm_comb_ops, _blinds_comb_ops) = dense.comb_ops.commit(&gens.gens_ops, false);
    let (comm_comb_mem, _blinds_comb_mem) = dense.comb_mem.commit(&gens.gens_mem, false);

    (
      SparseMatPolyCommitment {
        batch_size,
        num_mem_cells: dense.row.audit_ts.len(),
        num_ops: dense.row.read_ts[0].len(),
        comm_comb_ops,
        comm_comb_mem,
      },
      dense,
    )
  }
}

impl<F: PrimeField> MultiSparseMatPolynomialAsDense<F> {
  pub fn deref(&self, row_mem_val: &[F], col_mem_val: &[F]) -> Derefs<F> {
    let row_ops_val = self.row.deref(row_mem_val);
    let col_ops_val = self.col.deref(col_mem_val);

    Derefs::new(row_ops_val, col_ops_val)
  }
}

#[derive(Debug)]
struct ProductLayer<F: PrimeField> {
  init: ProductCircuit<F>,
  read_vec: Vec<ProductCircuit<F>>,
  write_vec: Vec<ProductCircuit<F>>,
  audit: ProductCircuit<F>,
}

#[derive(Debug)]
struct Layers<F: PrimeField> {
  prod_layer: ProductLayer<F>,
}

impl<F: PrimeField> Layers<F> {
  fn build_hash_layer(
    eval_table: &[F],
    addrs_vec: &[DensePolynomial<F>],
    derefs_vec: &[DensePolynomial<F>],
    read_ts_vec: &[DensePolynomial<F>],
    audit_ts: &DensePolynomial<F>,
    r_mem_check: &(F, F),
  ) -> (
    DensePolynomial<F>,
    Vec<DensePolynomial<F>>,
    Vec<DensePolynomial<F>>,
    DensePolynomial<F>,
  ) {
    let (r_hash, r_multiset_check) = r_mem_check;

    //hash(addr, val, ts) = ts * r_hash_sqr + val * r_hash + addr
    let r_hash_sqr = r_hash.square();
    let hash_func = |addr: &F, val: &F, ts: &F| -> F { r_hash_sqr * ts + (*val) * r_hash + addr };

    // hash init and audit that does not depend on #instances
    let num_mem_cells = eval_table.len();
    let poly_init_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at init time, addr is given by i, init value is given by eval_table, and ts = 0
          hash_func(&F::from(i as u64), &eval_table[i], &F::zero()) - r_multiset_check
        })
        .collect::<Vec<F>>(),
    );
    let poly_audit_hashed = DensePolynomial::new(
      (0..num_mem_cells)
        .map(|i| {
          // at audit time, addr is given by i, value is given by eval_table, and ts is given by audit_ts
          hash_func(&F::from(i as u64), &eval_table[i], &audit_ts[i]) - r_multiset_check
        })
        .collect::<Vec<F>>(),
    );

    // hash read and write that depends on #instances
    let mut poly_read_hashed_vec: Vec<DensePolynomial<F>> = Vec::new();
    let mut poly_write_hashed_vec: Vec<DensePolynomial<F>> = Vec::new();
    for i in 0..addrs_vec.len() {
      let (addrs, derefs, read_ts) = (&addrs_vec[i], &derefs_vec[i], &read_ts_vec[i]);
      assert_eq!(addrs.len(), derefs.len());
      assert_eq!(addrs.len(), read_ts.len());
      let num_ops = addrs.len();
      let poly_read_hashed = DensePolynomial::new(
        (0..num_ops)
          .map(|i| {
            // at read time, addr is given by addrs, value is given by derefs, and ts is given by read_ts
            hash_func(&addrs[i], &derefs[i], &read_ts[i]) - r_multiset_check
          })
          .collect::<Vec<F>>(),
      );
      poly_read_hashed_vec.push(poly_read_hashed);

      let poly_write_hashed = DensePolynomial::new(
        (0..num_ops)
          .map(|i| {
            // at write time, addr is given by addrs, value is given by derefs, and ts is given by write_ts = read_ts + 1
            hash_func(&addrs[i], &derefs[i], &(read_ts[i] + F::one())) - r_multiset_check
          })
          .collect::<Vec<F>>(),
      );
      poly_write_hashed_vec.push(poly_write_hashed);
    }

    (
      poly_init_hashed,
      poly_read_hashed_vec,
      poly_write_hashed_vec,
      poly_audit_hashed,
    )
  }

  pub fn new(
    eval_table: &[F],
    addr_timestamps: &AddrTimestamps<F>,
    poly_ops_val: &[DensePolynomial<F>],
    r_mem_check: &(F, F),
  ) -> Self {
    let (poly_init_hashed, poly_read_hashed_vec, poly_write_hashed_vec, poly_audit_hashed) =
      Layers::build_hash_layer(
        eval_table,
        &addr_timestamps.ops_addr,
        poly_ops_val,
        &addr_timestamps.read_ts,
        &addr_timestamps.audit_ts,
        r_mem_check,
      );

    let prod_init = ProductCircuit::new(&poly_init_hashed);
    let prod_read_vec = (0..poly_read_hashed_vec.len())
      .map(|i| ProductCircuit::new(&poly_read_hashed_vec[i]))
      .collect::<Vec<ProductCircuit<F>>>();
    let prod_write_vec = (0..poly_write_hashed_vec.len())
      .map(|i| ProductCircuit::new(&poly_write_hashed_vec[i]))
      .collect::<Vec<ProductCircuit<F>>>();
    let prod_audit = ProductCircuit::new(&poly_audit_hashed);

    // subset audit check
    let hashed_writes: F = (0..prod_write_vec.len())
      .map(|i| prod_write_vec[i].evaluate())
      .product();
    let hashed_write_set: F = prod_init.evaluate() * hashed_writes;

    let hashed_reads: F = (0..prod_read_vec.len())
      .map(|i| prod_read_vec[i].evaluate())
      .product();
    let hashed_read_set: F = hashed_reads * prod_audit.evaluate();

    //assert_eq!(hashed_read_set, hashed_write_set);
    debug_assert_eq!(hashed_read_set, hashed_write_set);

    Layers {
      prod_layer: ProductLayer {
        init: prod_init,
        read_vec: prod_read_vec,
        write_vec: prod_write_vec,
        audit: prod_audit,
      },
    }
  }
}

#[derive(Debug)]
struct PolyEvalNetwork<F: PrimeField> {
  row_layers: Layers<F>,
  col_layers: Layers<F>,
}

impl<F: PrimeField> PolyEvalNetwork<F> {
  pub fn new(
    dense: &MultiSparseMatPolynomialAsDense<F>,
    derefs: &Derefs<F>,
    mem_rx: &[F],
    mem_ry: &[F],
    r_mem_check: &(F, F),
  ) -> Self {
    let row_layers = Layers::new(mem_rx, &dense.row, &derefs.row_ops_val, r_mem_check);
    let col_layers = Layers::new(mem_ry, &dense.col, &derefs.col_ops_val, r_mem_check);

    PolyEvalNetwork {
      row_layers,
      col_layers,
    }
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct HashLayerProof<E: Pairing> {
  eval_row: (Vec<E::ScalarField>, Vec<E::ScalarField>, E::ScalarField),
  eval_col: (Vec<E::ScalarField>, Vec<E::ScalarField>, E::ScalarField),
  eval_val: Vec<E::ScalarField>,
  eval_derefs: (Vec<E::ScalarField>, Vec<E::ScalarField>),
  proof_ops: PolyEvalProof<E>,
  proof_mem: PolyEvalProof<E>,
  proof_derefs: DerefsEvalProof<E>,
}

impl<E> HashLayerProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  fn prove_helper(
    rand: (&Vec<E::ScalarField>, &Vec<E::ScalarField>),
    addr_timestamps: &AddrTimestamps<E::ScalarField>,
  ) -> (Vec<E::ScalarField>, Vec<E::ScalarField>, E::ScalarField) {
    let (rand_mem, rand_ops) = rand;

    // decommit ops-addr at rand_ops
    let mut eval_ops_addr_vec: Vec<E::ScalarField> = Vec::new();
    for i in 0..addr_timestamps.ops_addr.len() {
      let eval_ops_addr = addr_timestamps.ops_addr[i].evaluate(rand_ops);
      eval_ops_addr_vec.push(eval_ops_addr);
    }

    // decommit read_ts at rand_ops
    let mut eval_read_ts_vec: Vec<E::ScalarField> = Vec::new();
    for i in 0..addr_timestamps.read_ts.len() {
      let eval_read_ts = addr_timestamps.read_ts[i].evaluate(rand_ops);
      eval_read_ts_vec.push(eval_read_ts);
    }

    // decommit audit-ts at rand_mem
    let eval_audit_ts = addr_timestamps.audit_ts.evaluate(rand_mem);

    (eval_ops_addr_vec, eval_read_ts_vec, eval_audit_ts)
  }

  fn prove(
    rand: (&Vec<E::ScalarField>, &Vec<E::ScalarField>),
    dense: &MultiSparseMatPolynomialAsDense<E::ScalarField>,
    derefs: &Derefs<E::ScalarField>,
    gens: &SparseMatPolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Self {
    // transcript.append_protocol_name(HashLayerProof::protocol_name());

    let (rand_mem, rand_ops) = rand;

    // decommit derefs at rand_ops
    let eval_row_ops_val = (0..derefs.row_ops_val.len())
      .map(|i| derefs.row_ops_val[i].evaluate(rand_ops))
      .collect::<Vec<E::ScalarField>>();
    let eval_col_ops_val = (0..derefs.col_ops_val.len())
      .map(|i| derefs.col_ops_val[i].evaluate(rand_ops))
      .collect::<Vec<E::ScalarField>>();
    let proof_derefs = DerefsEvalProof::prove(
      derefs,
      &eval_row_ops_val,
      &eval_col_ops_val,
      rand_ops,
      &gens.gens_derefs,
      transcript,
    );
    let eval_derefs = (eval_row_ops_val, eval_col_ops_val);

    // evaluate row_addr, row_read-ts, col_addr, col_read-ts, val at rand_ops
    // evaluate row_audit_ts and col_audit_ts at rand_mem
    let (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts) =
      HashLayerProof::<E>::prove_helper((rand_mem, rand_ops), &dense.row);
    let (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts) =
      HashLayerProof::<E>::prove_helper((rand_mem, rand_ops), &dense.col);
    let eval_val_vec = (0..dense.val.len())
      .map(|i| dense.val[i].evaluate(rand_ops))
      .collect::<Vec<E::ScalarField>>();

    // form a single decommitment using comm_comb_ops
    let mut evals_ops: Vec<E::ScalarField> = Vec::new();
    evals_ops.extend(&eval_row_addr_vec);
    evals_ops.extend(&eval_row_read_ts_vec);
    evals_ops.extend(&eval_col_addr_vec);
    evals_ops.extend(&eval_col_read_ts_vec);
    evals_ops.extend(&eval_val_vec);
    evals_ops.resize(evals_ops.len().next_power_of_two(), E::ScalarField::zero());
    transcript.append_scalar_vector(b"", &evals_ops);
    let challenges_ops = transcript.challenge_scalar_vec(b"", evals_ops.len().log_2());

    let mut poly_evals_ops = DensePolynomial::new(evals_ops);
    for i in (0..challenges_ops.len()).rev() {
      poly_evals_ops.bound_poly_var_bot(&challenges_ops[i]);
    }
    assert_eq!(poly_evals_ops.len(), 1);
    let joint_claim_eval_ops = poly_evals_ops[0];
    let mut r_joint_ops = challenges_ops;
    r_joint_ops.extend(rand_ops);
    debug_assert_eq!(dense.comb_ops.evaluate(&r_joint_ops), joint_claim_eval_ops);
    transcript.append_scalar(b"", &joint_claim_eval_ops);
    let (proof_ops, _comm_ops_eval) = PolyEvalProof::prove(
      &dense.comb_ops,
      None,
      &r_joint_ops,
      &joint_claim_eval_ops,
      None,
      &gens.gens_ops,
      transcript,
    );

    // form a single decommitment using comb_comb_mem at rand_mem
    let evals_mem: Vec<E::ScalarField> = vec![eval_row_audit_ts, eval_col_audit_ts];
    // evals_mem.append_to_transcript(b"claim_evals_mem", transcript);
    transcript.append_scalar_vector(b"", &evals_mem);
    let challenges_mem = transcript.challenge_scalar_vec(b"", evals_mem.len().log_2());

    let mut poly_evals_mem = DensePolynomial::new(evals_mem);
    for i in (0..challenges_mem.len()).rev() {
      poly_evals_mem.bound_poly_var_bot(&challenges_mem[i]);
    }
    assert_eq!(poly_evals_mem.len(), 1);
    let joint_claim_eval_mem = poly_evals_mem[0];
    let mut r_joint_mem = challenges_mem;
    r_joint_mem.extend(rand_mem);
    debug_assert_eq!(dense.comb_mem.evaluate(&r_joint_mem), joint_claim_eval_mem);
    transcript.append_scalar(b"", &joint_claim_eval_mem);
    let (proof_mem, _comm_mem_eval) = PolyEvalProof::prove(
      &dense.comb_mem,
      None,
      &r_joint_mem,
      &joint_claim_eval_mem,
      None,
      &gens.gens_mem,
      transcript,
    );

    HashLayerProof {
      eval_row: (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts),
      eval_col: (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts),
      eval_val: eval_val_vec,
      eval_derefs,
      proof_ops,
      proof_mem,
      proof_derefs,
    }
  }

  fn verify_helper(
    rand: &(&Vec<E::ScalarField>, &Vec<E::ScalarField>),
    claims: &(
      E::ScalarField,
      Vec<E::ScalarField>,
      Vec<E::ScalarField>,
      E::ScalarField,
    ),
    eval_ops_val: &[E::ScalarField],
    eval_ops_addr: &[E::ScalarField],
    eval_read_ts: &[E::ScalarField],
    eval_audit_ts: &E::ScalarField,
    r: &[E::ScalarField],
    r_hash: &E::ScalarField,
    r_multiset_check: &E::ScalarField,
  ) -> Result<(), ProofVerifyError> {
    let r_hash_sqr = r_hash.square();
    let hash_func = |addr: &E::ScalarField,
                     val: &E::ScalarField,
                     ts: &E::ScalarField|
     -> E::ScalarField { r_hash_sqr * ts + (*val) * r_hash + addr };

    let (rand_mem, _rand_ops) = rand;
    let (claim_init, claim_read, claim_write, claim_audit) = claims;

    // init
    let eval_init_addr = IdentityPolynomial::new(rand_mem.len()).evaluate(rand_mem);
    let eval_init_val = EqPolynomial::new(r.to_vec()).evaluate(rand_mem);
    let hash_init_at_rand_mem =
      hash_func(&eval_init_addr, &eval_init_val, &E::ScalarField::zero()) - r_multiset_check; // verify the claim_last of init chunk
    assert_eq!(&hash_init_at_rand_mem, claim_init);

    // read
    for i in 0..eval_ops_addr.len() {
      let hash_read_at_rand_ops =
        hash_func(&eval_ops_addr[i], &eval_ops_val[i], &eval_read_ts[i]) - r_multiset_check; // verify the claim_last of init chunk
      assert_eq!(&hash_read_at_rand_ops, &claim_read[i]);
    }

    // write: shares addr, val component; only decommit write_ts
    for i in 0..eval_ops_addr.len() {
      let eval_write_ts = eval_read_ts[i] + E::ScalarField::one();
      let hash_write_at_rand_ops =
        hash_func(&eval_ops_addr[i], &eval_ops_val[i], &eval_write_ts) - r_multiset_check; // verify the claim_last of init chunk
      assert_eq!(&hash_write_at_rand_ops, &claim_write[i]);
    }

    // audit: shares addr and val with init
    let eval_audit_addr = eval_init_addr;
    let eval_audit_val = eval_init_val;
    let hash_audit_at_rand_mem =
      hash_func(&eval_audit_addr, &eval_audit_val, eval_audit_ts) - r_multiset_check;
    assert_eq!(&hash_audit_at_rand_mem, claim_audit); // verify the last step of the sum-check for audit

    Ok(())
  }

  fn verify(
    &self,
    rand: (&Vec<E::ScalarField>, &Vec<E::ScalarField>),
    claims_row: &(
      E::ScalarField,
      Vec<E::ScalarField>,
      Vec<E::ScalarField>,
      E::ScalarField,
    ),
    claims_col: &(
      E::ScalarField,
      Vec<E::ScalarField>,
      Vec<E::ScalarField>,
      E::ScalarField,
    ),
    claims_dotp: &[E::ScalarField],
    comm: &SparseMatPolyCommitment<E::G1>,
    gens: &SparseMatPolyCommitmentGens<E>,
    comm_derefs: &DerefsCommitment<E::G1>,
    rx: &[E::ScalarField],
    ry: &[E::ScalarField],
    r_hash: &E::ScalarField,
    r_multiset_check: &E::ScalarField,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Result<(), ProofVerifyError> {
    let timer = Timer::new("verify_hash_proof");
    // transcript.append_protocol_name(HashLayerProof::protocol_name());

    let (rand_mem, rand_ops) = rand;

    // verify derefs at rand_ops
    let (eval_row_ops_val, eval_col_ops_val) = &self.eval_derefs;
    assert_eq!(eval_row_ops_val.len(), eval_col_ops_val.len());
    self.proof_derefs.verify(
      rand_ops,
      eval_row_ops_val,
      eval_col_ops_val,
      &gens.gens_derefs,
      comm_derefs,
      transcript,
    )?;

    // verify the decommitments used in evaluation sum-check
    let eval_val_vec = &self.eval_val;
    assert_eq!(claims_dotp.len(), 3 * eval_row_ops_val.len());
    for i in 0..claims_dotp.len() / 3 {
      let claim_row_ops_val = claims_dotp[3 * i];
      let claim_col_ops_val = claims_dotp[3 * i + 1];
      let claim_val = claims_dotp[3 * i + 2];

      assert_eq!(claim_row_ops_val, eval_row_ops_val[i]);
      assert_eq!(claim_col_ops_val, eval_col_ops_val[i]);
      assert_eq!(claim_val, eval_val_vec[i]);
    }

    // verify addr-timestamps using comm_comb_ops at rand_ops
    let (eval_row_addr_vec, eval_row_read_ts_vec, eval_row_audit_ts) = &self.eval_row;
    let (eval_col_addr_vec, eval_col_read_ts_vec, eval_col_audit_ts) = &self.eval_col;

    let mut evals_ops: Vec<E::ScalarField> = Vec::new();
    evals_ops.extend(eval_row_addr_vec);
    evals_ops.extend(eval_row_read_ts_vec);
    evals_ops.extend(eval_col_addr_vec);
    evals_ops.extend(eval_col_read_ts_vec);
    evals_ops.extend(eval_val_vec);
    evals_ops.resize(evals_ops.len().next_power_of_two(), E::ScalarField::zero());
    transcript.append_scalar_vector(b"", &evals_ops);
    // evals_ops.append_to_transcript(b"claim_evals_ops", transcript);
    let challenges_ops = transcript.challenge_scalar_vec(b"", evals_ops.len().log_2());

    let mut poly_evals_ops = DensePolynomial::new(evals_ops);
    for i in (0..challenges_ops.len()).rev() {
      poly_evals_ops.bound_poly_var_bot(&challenges_ops[i]);
    }
    assert_eq!(poly_evals_ops.len(), 1);
    let joint_claim_eval_ops = poly_evals_ops[0];
    let mut r_joint_ops = challenges_ops;
    r_joint_ops.extend(rand_ops);
    transcript.append_scalar(b"", &joint_claim_eval_ops);
    assert!(self
      .proof_ops
      .verify_plain(
        &gens.gens_ops,
        transcript,
        &r_joint_ops,
        &joint_claim_eval_ops,
        &comm.comm_comb_ops
      )
      .is_ok());

    // verify proof-mem using comm_comb_mem at rand_mem
    // form a single decommitment using comb_comb_mem at rand_mem
    let evals_mem: Vec<E::ScalarField> = vec![*eval_row_audit_ts, *eval_col_audit_ts];
    // evals_mem.append_to_transcript(b"claim_evals_mem", transcript);
    transcript.append_scalar_vector(b"", &evals_mem);
    let challenges_mem = transcript.challenge_scalar_vec(b"", evals_mem.len().log_2());

    let mut poly_evals_mem = DensePolynomial::new(evals_mem);
    for i in (0..challenges_mem.len()).rev() {
      poly_evals_mem.bound_poly_var_bot(&challenges_mem[i]);
    }
    assert_eq!(poly_evals_mem.len(), 1);
    let joint_claim_eval_mem = poly_evals_mem[0];
    let mut r_joint_mem = challenges_mem;
    r_joint_mem.extend(rand_mem);
    // joint_claim_eval_mem.append_to_transcript(b"joint_claim_eval_mem", transcript);
    transcript.append_scalar(b"", &joint_claim_eval_mem);
    self.proof_mem.verify_plain(
      &gens.gens_mem,
      transcript,
      &r_joint_mem,
      &joint_claim_eval_mem,
      &comm.comm_comb_mem,
    )?;

    // verify the claims from the product layer
    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = &self.eval_row;
    HashLayerProof::<E>::verify_helper(
      &(rand_mem, rand_ops),
      claims_row,
      eval_row_ops_val,
      eval_ops_addr,
      eval_read_ts,
      eval_audit_ts,
      rx,
      r_hash,
      r_multiset_check,
    )?;

    let (eval_ops_addr, eval_read_ts, eval_audit_ts) = &self.eval_col;
    HashLayerProof::<E>::verify_helper(
      &(rand_mem, rand_ops),
      claims_col,
      eval_col_ops_val,
      eval_ops_addr,
      eval_read_ts,
      eval_audit_ts,
      ry,
      r_hash,
      r_multiset_check,
    )?;

    timer.stop();
    Ok(())
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct ProductLayerProof<F: PrimeField> {
  eval_row: (F, Vec<F>, Vec<F>, F),
  eval_col: (F, Vec<F>, Vec<F>, F),
  eval_val: (Vec<F>, Vec<F>),
  proof_mem: ProductCircuitEvalProofBatched<F>,
  proof_ops: ProductCircuitEvalProofBatched<F>,
}

impl<F: PrimeField + Absorb> ProductLayerProof<F> {
  pub fn prove(
    row_prod_layer: &mut ProductLayer<F>,
    col_prod_layer: &mut ProductLayer<F>,
    dense: &MultiSparseMatPolynomialAsDense<F>,
    derefs: &Derefs<F>,
    eval: &[F],
    transcript: &mut PoseidonTranscript<F>,
  ) -> (Self, Vec<F>, Vec<F>) {
    // transcript.append_protocol_name(ProductLayerProof::protocol_name());

    let row_eval_init = row_prod_layer.init.evaluate();
    let row_eval_audit = row_prod_layer.audit.evaluate();
    let row_eval_read = (0..row_prod_layer.read_vec.len())
      .map(|i| row_prod_layer.read_vec[i].evaluate())
      .collect::<Vec<F>>();
    let row_eval_write = (0..row_prod_layer.write_vec.len())
      .map(|i| row_prod_layer.write_vec[i].evaluate())
      .collect::<Vec<F>>();

    // subset check
    let ws: F = (0..row_eval_write.len())
      .map(|i| row_eval_write[i])
      .product();
    let rs: F = (0..row_eval_read.len()).map(|i| row_eval_read[i]).product();
    assert_eq!(row_eval_init * ws, rs * row_eval_audit);

    transcript.append_scalar(b"", &row_eval_init);
    transcript.append_scalar_vector(b"", &row_eval_read);
    transcript.append_scalar_vector(b"", &row_eval_write);
    transcript.append_scalar(b"", &row_eval_audit);

    let col_eval_init = col_prod_layer.init.evaluate();
    let col_eval_audit = col_prod_layer.audit.evaluate();
    let col_eval_read: Vec<F> = (0..col_prod_layer.read_vec.len())
      .map(|i| col_prod_layer.read_vec[i].evaluate())
      .collect();
    let col_eval_write: Vec<F> = (0..col_prod_layer.write_vec.len())
      .map(|i| col_prod_layer.write_vec[i].evaluate())
      .collect();

    // subset check
    let ws: F = (0..col_eval_write.len())
      .map(|i| col_eval_write[i])
      .product();
    let rs: F = (0..col_eval_read.len()).map(|i| col_eval_read[i]).product();
    assert_eq!(col_eval_init * ws, rs * col_eval_audit);

    transcript.append_scalar(b"", &col_eval_init);
    transcript.append_scalar_vector(b"", &col_eval_read);
    transcript.append_scalar_vector(b"", &col_eval_write);
    transcript.append_scalar(b"", &col_eval_audit);

    // prepare dotproduct circuit for batching then with ops-related product circuits
    assert_eq!(eval.len(), derefs.row_ops_val.len());
    assert_eq!(eval.len(), derefs.col_ops_val.len());
    assert_eq!(eval.len(), dense.val.len());
    let mut dotp_circuit_left_vec: Vec<DotProductCircuit<F>> = Vec::new();
    let mut dotp_circuit_right_vec: Vec<DotProductCircuit<F>> = Vec::new();
    let mut eval_dotp_left_vec: Vec<F> = Vec::new();
    let mut eval_dotp_right_vec: Vec<F> = Vec::new();
    for i in 0..derefs.row_ops_val.len() {
      // evaluate sparse polynomial evaluation using two dotp checks
      let left = derefs.row_ops_val[i].clone();
      let right = derefs.col_ops_val[i].clone();
      let weights = dense.val[i].clone();

      // build two dot product circuits to prove evaluation of sparse polynomial
      let mut dotp_circuit = DotProductCircuit::new(left, right, weights);
      let (dotp_circuit_left, dotp_circuit_right) = dotp_circuit.split();

      let (eval_dotp_left, eval_dotp_right) =
        (dotp_circuit_left.evaluate(), dotp_circuit_right.evaluate());

      // eval_dotp_left.append_to_transcript(b"claim_eval_dotp_left", transcript);
      // eval_dotp_right.append_to_transcript(b"claim_eval_dotp_right", transcript);
      transcript.append_scalar(b"", &eval_dotp_left);
      transcript.append_scalar(b"", &eval_dotp_right);
      assert_eq!(eval_dotp_left + eval_dotp_right, eval[i]);
      eval_dotp_left_vec.push(eval_dotp_left);
      eval_dotp_right_vec.push(eval_dotp_right);

      dotp_circuit_left_vec.push(dotp_circuit_left);
      dotp_circuit_right_vec.push(dotp_circuit_right);
    }

    // The number of operations into the memory encoded by rx and ry are always the same (by design)
    // So we can produce a batched product proof for all of them at the same time.
    // prove the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    // TODO: we currently only produce proofs for 3 batched sparse polynomial evaluations
    assert_eq!(row_prod_layer.read_vec.len(), 3);
    let (row_read_A, row_read_B, row_read_C) = {
      let (vec_A, vec_BC) = row_prod_layer.read_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (row_write_A, row_write_B, row_write_C) = {
      let (vec_A, vec_BC) = row_prod_layer.write_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (col_read_A, col_read_B, col_read_C) = {
      let (vec_A, vec_BC) = col_prod_layer.read_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (col_write_A, col_write_B, col_write_C) = {
      let (vec_A, vec_BC) = col_prod_layer.write_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (dotp_left_A, dotp_left_B, dotp_left_C) = {
      let (vec_A, vec_BC) = dotp_circuit_left_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (dotp_right_A, dotp_right_B, dotp_right_C) = {
      let (vec_A, vec_BC) = dotp_circuit_right_vec.split_at_mut(1);
      let (vec_B, vec_C) = vec_BC.split_at_mut(1);
      (vec_A, vec_B, vec_C)
    };

    let (proof_ops, rand_ops) = ProductCircuitEvalProofBatched::prove(
      &mut vec![
        &mut row_read_A[0],
        &mut row_read_B[0],
        &mut row_read_C[0],
        &mut row_write_A[0],
        &mut row_write_B[0],
        &mut row_write_C[0],
        &mut col_read_A[0],
        &mut col_read_B[0],
        &mut col_read_C[0],
        &mut col_write_A[0],
        &mut col_write_B[0],
        &mut col_write_C[0],
      ],
      &mut vec![
        &mut dotp_left_A[0],
        &mut dotp_right_A[0],
        &mut dotp_left_B[0],
        &mut dotp_right_B[0],
        &mut dotp_left_C[0],
        &mut dotp_right_C[0],
      ],
      transcript,
    );

    // produce a batched proof of memory-related product circuits
    let (proof_mem, rand_mem) = ProductCircuitEvalProofBatched::prove(
      &mut vec![
        &mut row_prod_layer.init,
        &mut row_prod_layer.audit,
        &mut col_prod_layer.init,
        &mut col_prod_layer.audit,
      ],
      &mut Vec::new(),
      transcript,
    );

    let product_layer_proof = ProductLayerProof {
      eval_row: (row_eval_init, row_eval_read, row_eval_write, row_eval_audit),
      eval_col: (col_eval_init, col_eval_read, col_eval_write, col_eval_audit),
      eval_val: (eval_dotp_left_vec, eval_dotp_right_vec),
      proof_mem,
      proof_ops,
    };

    let mut product_layer_proof_encoded: Vec<u8> = Vec::new();
    product_layer_proof
      .serialize_with_mode(&mut product_layer_proof_encoded, Compress::Yes)
      .unwrap();
    let msg = format!(
      "len_product_layer_proof {:?}",
      product_layer_proof_encoded.len()
    );
    Timer::print(&msg);

    (product_layer_proof, rand_mem, rand_ops)
  }

  pub fn verify(
    &self,
    num_ops: usize,
    num_cells: usize,
    eval: &[F],
    transcript: &mut PoseidonTranscript<F>,
  ) -> Result<(Vec<F>, Vec<F>, Vec<F>, Vec<F>, Vec<F>), ProofVerifyError> {
    // transcript.append_protocol_name(ProductLayerProof::protocol_name());

    let timer = Timer::new("verify_prod_proof");
    let num_instances = eval.len();

    // subset check
    let (row_eval_init, row_eval_read, row_eval_write, row_eval_audit) = &self.eval_row;
    assert_eq!(row_eval_write.len(), num_instances);
    assert_eq!(row_eval_read.len(), num_instances);
    let ws: F = (0..row_eval_write.len())
      .map(|i| row_eval_write[i])
      .product();
    let rs: F = (0..row_eval_read.len()).map(|i| row_eval_read[i]).product();
    assert_eq!(ws * row_eval_init, rs * row_eval_audit);

    // row_eval_init.append_to_transcript(b"claim_row_eval_init", transcript);
    // row_eval_read.append_to_transcript(b"claim_row_eval_read", transcript);
    // row_eval_write.append_to_transcript(b"claim_row_eval_write", transcript);
    // row_eval_audit.append_to_transcript(b"claim_row_eval_audit", transcript);

    transcript.append_scalar(b"", row_eval_init);
    transcript.append_scalar_vector(b"", row_eval_read);
    transcript.append_scalar_vector(b"", row_eval_write);
    transcript.append_scalar(b"", row_eval_audit);

    // subset check
    let (col_eval_init, col_eval_read, col_eval_write, col_eval_audit) = &self.eval_col;
    assert_eq!(col_eval_write.len(), num_instances);
    assert_eq!(col_eval_read.len(), num_instances);
    let ws: F = (0..col_eval_write.len())
      .map(|i| col_eval_write[i])
      .product();
    let rs: F = (0..col_eval_read.len()).map(|i| col_eval_read[i]).product();
    assert_eq!(ws * col_eval_init, rs * col_eval_audit);

    // col_eval_init.append_to_transcript(b"claim_col_eval_init", transcript);
    // col_eval_read.append_to_transcript(b"claim_col_eval_read", transcript);
    // col_eval_write.append_to_transcript(b"claim_col_eval_write", transcript);
    // col_eval_audit.append_to_transcript(b"claim_col_eval_audit", transcript);

    transcript.append_scalar(b"", col_eval_init);
    transcript.append_scalar_vector(b"", col_eval_read);
    transcript.append_scalar_vector(b"", col_eval_write);
    transcript.append_scalar(b"", col_eval_audit);

    // verify the evaluation of the sparse polynomial
    let (eval_dotp_left, eval_dotp_right) = &self.eval_val;
    assert_eq!(eval_dotp_left.len(), eval_dotp_left.len());
    assert_eq!(eval_dotp_left.len(), num_instances);
    let mut claims_dotp_circuit: Vec<F> = Vec::new();
    for i in 0..num_instances {
      assert_eq!(eval_dotp_left[i] + eval_dotp_right[i], eval[i]);
      // eval_dotp_left[i].append_to_transcript(b"claim_eval_dotp_left", transcript);
      // eval_dotp_right[i].append_to_transcript(b"claim_eval_dotp_right", transcript)
      transcript.append_scalar(b"", &eval_dotp_left[i]);
      transcript.append_scalar(b"", &eval_dotp_right[i]);

      claims_dotp_circuit.push(eval_dotp_left[i]);
      claims_dotp_circuit.push(eval_dotp_right[i]);
    }

    // verify the correctness of claim_row_eval_read, claim_row_eval_write, claim_col_eval_read, and claim_col_eval_write
    let mut claims_prod_circuit: Vec<F> = Vec::new();
    claims_prod_circuit.extend(row_eval_read);
    claims_prod_circuit.extend(row_eval_write);
    claims_prod_circuit.extend(col_eval_read);
    claims_prod_circuit.extend(col_eval_write);

    let (claims_ops, claims_dotp, rand_ops) = self.proof_ops.verify(
      &claims_prod_circuit,
      &claims_dotp_circuit,
      num_ops,
      transcript,
    );
    // verify the correctness of claim_row_eval_init and claim_row_eval_audit
    let (claims_mem, _claims_mem_dotp, rand_mem) = self.proof_mem.verify(
      &[
        *row_eval_init,
        *row_eval_audit,
        *col_eval_init,
        *col_eval_audit,
      ],
      &Vec::new(),
      num_cells,
      transcript,
    );
    timer.stop();

    Ok((claims_mem, rand_mem, claims_ops, claims_dotp, rand_ops))
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
struct PolyEvalNetworkProof<E: Pairing> {
  proof_prod_layer: ProductLayerProof<E::ScalarField>,
  proof_hash_layer: HashLayerProof<E>,
}

impl<E> PolyEvalNetworkProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  pub fn prove(
    network: &mut PolyEvalNetwork<E::ScalarField>,
    dense: &MultiSparseMatPolynomialAsDense<E::ScalarField>,
    derefs: &Derefs<E::ScalarField>,
    evals: &[E::ScalarField],
    gens: &SparseMatPolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Self {
    // transcript.append_protocol_name(PolyEvalNetworkProof::protocol_name());

    let (proof_prod_layer, rand_mem, rand_ops) = ProductLayerProof::prove(
      &mut network.row_layers.prod_layer,
      &mut network.col_layers.prod_layer,
      dense,
      derefs,
      evals,
      transcript,
    );

    // proof of hash layer for row and col
    let proof_hash_layer =
      HashLayerProof::prove((&rand_mem, &rand_ops), dense, derefs, gens, transcript);

    PolyEvalNetworkProof {
      proof_prod_layer,
      proof_hash_layer,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment<E::G1>,
    comm_derefs: &DerefsCommitment<E::G1>,
    evals: &[E::ScalarField],
    gens: &SparseMatPolyCommitmentGens<E>,
    rx: &[E::ScalarField],
    ry: &[E::ScalarField],
    r_mem_check: &(E::ScalarField, E::ScalarField),
    nz: usize,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Result<(), ProofVerifyError> {
    let timer = Timer::new("verify_polyeval_proof");
    // transcript.append_protocol_name(PolyEvalNetworkProof::protocol_name());

    let num_instances = evals.len();
    let (r_hash, r_multiset_check) = r_mem_check;

    let num_ops = nz.next_power_of_two();
    let num_cells = rx.len().pow2();
    assert_eq!(rx.len(), ry.len());

    let (claims_mem, rand_mem, mut claims_ops, claims_dotp, rand_ops) = self
      .proof_prod_layer
      .verify(num_ops, num_cells, evals, transcript)?;
    assert_eq!(claims_mem.len(), 4);
    assert_eq!(claims_ops.len(), 4 * num_instances);
    assert_eq!(claims_dotp.len(), 3 * num_instances);

    let (claims_ops_row, claims_ops_col) = claims_ops.split_at_mut(2 * num_instances);
    let (claims_ops_row_read, claims_ops_row_write) = claims_ops_row.split_at_mut(num_instances);
    let (claims_ops_col_read, claims_ops_col_write) = claims_ops_col.split_at_mut(num_instances);

    // verify the proof of hash layer
    self.proof_hash_layer.verify(
      (&rand_mem, &rand_ops),
      &(
        claims_mem[0],
        claims_ops_row_read.to_vec(),
        claims_ops_row_write.to_vec(),
        claims_mem[1],
      ),
      &(
        claims_mem[2],
        claims_ops_col_read.to_vec(),
        claims_ops_col_write.to_vec(),
        claims_mem[3],
      ),
      &claims_dotp,
      comm,
      gens,
      comm_derefs,
      rx,
      ry,
      r_hash,
      r_multiset_check,
      transcript,
    )?;
    timer.stop();

    Ok(())
  }
}

#[derive(Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SparseMatPolyEvalProof<E: Pairing> {
  comm_derefs: DerefsCommitment<E::G1>,
  poly_eval_network_proof: PolyEvalNetworkProof<E>,
}

impl<E> SparseMatPolyEvalProof<E>
where
  E: Pairing,
  E::ScalarField: Absorb,
{
  fn equalize(
    rx: &[E::ScalarField],
    ry: &[E::ScalarField],
  ) -> (Vec<E::ScalarField>, Vec<E::ScalarField>) {
    match rx.len().cmp(&ry.len()) {
      Ordering::Less => {
        let diff = ry.len() - rx.len();
        let mut rx_ext = vec![E::ScalarField::zero(); diff];
        rx_ext.extend(rx);
        (rx_ext, ry.to_vec())
      }
      Ordering::Greater => {
        let diff = rx.len() - ry.len();
        let mut ry_ext = vec![E::ScalarField::zero(); diff];
        ry_ext.extend(ry);
        (rx.to_vec(), ry_ext)
      }
      Ordering::Equal => (rx.to_vec(), ry.to_vec()),
    }
  }

  pub fn prove(
    dense: &MultiSparseMatPolynomialAsDense<E::ScalarField>,
    rx: &[E::ScalarField], // point at which the polynomial is evaluated
    ry: &[E::ScalarField],
    evals: &[E::ScalarField], // a vector evaluation of \widetilde{M}(r = (rx,ry)) for each M
    gens: &SparseMatPolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> SparseMatPolyEvalProof<E> {
    // transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    // ensure there is one eval for each polynomial in dense
    assert_eq!(evals.len(), dense.batch_size);

    let (mem_rx, mem_ry) = {
      // equalize the lengths of rx and ry
      let (rx_ext, ry_ext) = SparseMatPolyEvalProof::<E>::equalize(rx, ry);
      let poly_rx = EqPolynomial::new(rx_ext).evals();
      let poly_ry = EqPolynomial::new(ry_ext).evals();
      (poly_rx, poly_ry)
    };

    let derefs = dense.deref(&mem_rx, &mem_ry);

    // commit to non-deterministic choices of the prover
    let timer_commit = Timer::new("commit_nondet_witness");
    let comm_derefs = {
      let comm = derefs.commit(&gens.gens_derefs);
      comm.write_to_transcript(transcript);
      comm
    };
    timer_commit.stop();

    let poly_eval_network_proof = {
      // produce a random element from the transcript for hash function
      let r_mem_check = transcript.challenge_scalar_vec(b"", 2);

      // build a network to evaluate the sparse polynomial
      let timer_build_network = Timer::new("build_layered_network");
      let mut net = PolyEvalNetwork::new(
        dense,
        &derefs,
        &mem_rx,
        &mem_ry,
        &(r_mem_check[0], r_mem_check[1]),
      );
      timer_build_network.stop();

      let timer_eval_network = Timer::new("evalproof_layered_network");
      let poly_eval_network_proof =
        PolyEvalNetworkProof::prove(&mut net, dense, &derefs, evals, gens, transcript);
      timer_eval_network.stop();

      poly_eval_network_proof
    };

    SparseMatPolyEvalProof {
      comm_derefs,
      poly_eval_network_proof,
    }
  }

  pub fn verify(
    &self,
    comm: &SparseMatPolyCommitment<E::G1>,
    rx: &[E::ScalarField], // point at which the polynomial is evaluated
    ry: &[E::ScalarField],
    evals: &[E::ScalarField], // evaluation of \widetilde{M}(r = (rx,ry))
    gens: &SparseMatPolyCommitmentGens<E>,
    transcript: &mut PoseidonTranscript<E::ScalarField>,
  ) -> Result<(), ProofVerifyError> {
    // transcript.append_protocol_name(SparseMatPolyEvalProof::protocol_name());

    // equalize the lengths of rx and ry
    let (rx_ext, ry_ext) = SparseMatPolyEvalProof::<E>::equalize(rx, ry);

    let (nz, num_mem_cells) = (comm.num_ops, comm.num_mem_cells);
    assert_eq!(rx_ext.len().pow2(), num_mem_cells);

    // add claims to transcript and obtain challenges for randomized mem-check circuit
    self.comm_derefs.write_to_transcript(transcript);

    // produce a random element from the transcript for hash function
    let r_mem_check = transcript.challenge_scalar_vec(b"", 2);

    self.poly_eval_network_proof.verify(
      comm,
      &self.comm_derefs,
      evals,
      gens,
      &rx_ext,
      &ry_ext,
      &(r_mem_check[0], r_mem_check[1]),
      nz,
      transcript,
    )
  }
}

#[derive(Clone)]
pub struct SparsePolyEntry<F: PrimeField> {
  pub idx: usize,
  pub val: F,
}

impl<F: PrimeField> SparsePolyEntry<F> {
  pub fn new(idx: usize, val: F) -> Self {
    SparsePolyEntry { idx, val }
  }
}
#[derive(Clone)]
pub struct SparsePolynomial<F: PrimeField> {
  pub num_vars: usize,
  pub Z: Vec<SparsePolyEntry<F>>,
}

impl<F: PrimeField> SparsePolynomial<F> {
  pub fn new(num_vars: usize, Z: Vec<SparsePolyEntry<F>>) -> Self {
    SparsePolynomial { num_vars, Z }
  }

  // fn compute_chi(a: &[bool], r: &[F]) -> F {
  //   assert_eq!(a.len(), r.len());
  //   let mut chi_i = F::one();
  //   for j in 0..r.len() {
  //     if a[j] {
  //       chi_i *= r[j];
  //     } else {
  //       chi_i *= F::one() - r[j];
  //     }
  //   }
  //   chi_i
  // }

  // // Takes O(n log n). TODO: do this in O(n) where n is the number of entries in Z
  // pub fn evaluate(&self, r: &[F]) -> F {
  //   assert_eq!(self.num_vars, r.len());

  //   (0..self.Z.len())
  //     .map(|i| {
  //       let bits = self.Z[i].idx.get_bits(r.len());
  //       println!("{:?}", bits);
  //       SparsePolynomial::compute_chi(&bits, r) * self.Z[i].val
  //     })
  //     .sum()
  // }
}

#[cfg(test)]
mod tests {
  use crate::parameters::poseidon_params;

  use super::*;
  use ark_std::UniformRand;
  use rand::RngCore;

  type F = ark_bls12_377::Fr;
  type E = ark_bls12_377::Bls12_377;
  #[test]
  fn check_sparse_polyeval_proof() {
    let mut rng = ark_std::rand::thread_rng();

    let num_nz_entries: usize = 256;
    let num_rows: usize = 256;
    let num_cols: usize = 256;
    let num_vars_x: usize = num_rows.log_2();
    let num_vars_y: usize = num_cols.log_2();

    let mut M: Vec<SparseMatEntry<F>> = Vec::new();

    for _i in 0..num_nz_entries {
      M.push(SparseMatEntry::new(
        (rng.next_u64() % (num_rows as u64)) as usize,
        (rng.next_u64() % (num_cols as u64)) as usize,
        F::rand(&mut rng),
      ));
    }

    let poly_M = SparseMatPolynomial::new(num_vars_x, num_vars_y, M);
    let gens = SparseMatPolyCommitmentGens::<E>::setup(
      b"gens_sparse_poly",
      num_vars_x,
      num_vars_y,
      num_nz_entries,
      3,
    );

    // commitment
    let (poly_comm, dense) = SparseMatPolynomial::multi_commit(&[&poly_M, &poly_M, &poly_M], &gens);

    // evaluation
    let rx: Vec<F> = (0..num_vars_x)
      .map(|_i| F::rand(&mut rng))
      .collect::<Vec<F>>();
    let ry: Vec<F> = (0..num_vars_y)
      .map(|_i| F::rand(&mut rng))
      .collect::<Vec<F>>();
    let eval = SparseMatPolynomial::multi_evaluate(&[&poly_M], &rx, &ry);
    let evals = vec![eval[0], eval[0], eval[0]];

    let params = poseidon_params();
    let mut prover_transcript = PoseidonTranscript::new(&params);
    let proof =
      SparseMatPolyEvalProof::prove(&dense, &rx, &ry, &evals, &gens, &mut prover_transcript);

    let mut verifier_transcript = PoseidonTranscript::new(&params);
    assert!(proof
      .verify(
        &poly_comm,
        &rx,
        &ry,
        &evals,
        &gens,
        &mut verifier_transcript,
      )
      .is_ok());
  }
}
