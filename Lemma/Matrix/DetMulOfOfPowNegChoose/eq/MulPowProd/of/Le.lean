import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
import Lemma.Matrix.GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le
import Syntax.LinearAlgebra.Matrix.Notation
open Matrix Nat


@[path]
private lemma main
  [Field R] [CharZero R]
  {d m : ℕ}
  {x δ : R}
-- given
  (h : d ≤ m) :
-- imply
  (([i < d, j < m] x ^ (j : ℕ) * ((j : R) + δ) ^ (i : ℕ)) *
    ([k < m, j < d] (-x) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : R))).det =
    x ^ (d.choose 2) * ∏ i ∈ Finset.range d, (i ! : R) := by
-- proof
  rw [Det.eq.Prod.of.All_All_Eq_0]
  ·
    simp only [GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le h, fwdDiff_iter_eq_factorial, Pi.natCast_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun i => i) d, Finset.sum_range_id, ← Nat.choose_two_right,
      Fin.prod_univ_eq_prod_range (fun i => (i ! : R)) d]
  ·
    intro i j hij
    rw [GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le h, fwdDiff_iter_pow_eq_zero_of_lt (show (i : ℕ) < j from hij), Pi.zero_apply, mul_zero]


-- created on 2026-10-07
-- updated on 2026-10-25
