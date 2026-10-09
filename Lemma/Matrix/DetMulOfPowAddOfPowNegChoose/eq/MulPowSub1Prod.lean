import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf_PowAdd.eq.ProdFactorial
import Lemma.Matrix.MulOfPowAddOfPowNegChoose.eq.MulOfChooseSumOf
import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
open Matrix Nat


@[path]
private lemma main
  {m d : ℕ}
  {δ l : ℝ} :
-- imply
  ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    (1 - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  rw [MulOfPowAddOfPowNegChoose.eq.MulOfChooseSumOf, Matrix.det_mul, DetOf_PowAdd.eq.ProdFactorial, Det.eq.Prod.of.All_All_Eq_0, Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) (m - d)]
  ·
    congr 1
    simp only [Matrix.of_apply, Nat.choose_self, Nat.cast_one, one_mul, sub_self, zpow_zero, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    congr 1
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  ·
    intro i j hij
    simp only [Matrix.of_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul]


-- created on 2026-10-07
