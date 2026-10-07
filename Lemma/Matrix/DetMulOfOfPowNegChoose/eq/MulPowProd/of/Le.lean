import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
import Lemma.Matrix.GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le
open Matrix Nat


@[main]
private lemma main
  {d m : ℕ}
  {x δ : ℝ}
-- given
  (h : d ≤ m) :
-- imply
  ((Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (k : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ))).det =
    x ^ (d.choose 2) * ∏ i ∈ Finset.range d, (i ! : ℝ) := by
-- proof
  rw [Det.eq.Prod.of.All_All_Eq_0]
  ·
    simp only [GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le h, fwdDiff_iter_eq_factorial, Pi.natCast_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun i => i) d, Finset.sum_range_id, ← Nat.choose_two_right,
      Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) d]
  ·
    intro i j hij
    rw [GetMulOfOfPowNegChoose.eq.MulPowFwdDiff.of.Le h, fwdDiff_iter_pow_eq_zero_of_lt (show (i : ℕ) < j from hij), Pi.zero_apply, mul_zero]


-- created on 2026-10-07
