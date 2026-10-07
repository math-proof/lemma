import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic
import Lemma.Matrix.DetOf_PowAdd.eq.ProdFactorial
import Lemma.Matrix.MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf
import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
open Matrix Nat


@[main]
private lemma main
  {m d : ℕ}
  {x δ l : ℝ} :
-- imply
  ((Matrix.of fun (i : Fin (m - d)) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0))).det =
    x ^ ((m - d).choose 2) * (x - l) ^ (d * (m - d)) * ∏ i ∈ Finset.range (m - d), (i ! : ℝ) := by
-- proof
  rw [MulOfMulPowOfPowNegChoose.eq.MulOfChooseSumOf, Matrix.det_mul, Det.eq.Prod.of.All_All_Eq_0]
  ·
    have hD : (Matrix.of fun (i : Fin (m - d)) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) =
        (Matrix.of fun (i j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ)) * (Matrix.diagonal (fun j : Fin (m - d) => x ^ (j : ℕ)) : Matrix (Fin (m - d)) (Fin (m - d)) ℝ) := by
      ext i j
      simp [Matrix.mul_diagonal]
    rw [hD, Matrix.det_mul, DetOf_PowAdd.eq.ProdFactorial, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum,
      Fin.sum_univ_eq_sum_range (fun i => i) (m - d), Finset.sum_range_id, ← Nat.choose_two_right,
      Fin.prod_univ_eq_prod_range (fun i => (i ! : ℝ)) (m - d)]
    simp only [Matrix.of_apply, Nat.choose_self, Nat.cast_one, one_mul, sub_self, zpow_zero, mul_one]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    have e : ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h = (x - l) ^ d := by
      rw [sub_eq_add_neg, add_pow]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [e]
    ring
  ·
    intro i j hij
    simp only [Matrix.of_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul]


-- created on 2026-10-07
