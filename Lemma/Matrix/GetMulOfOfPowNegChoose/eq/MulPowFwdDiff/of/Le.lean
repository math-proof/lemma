import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic


@[main]
private lemma main
  {d m : ℕ}
  {x δ : ℝ}
-- given
  (h : d ≤ m)
  (i j : Fin d) :
-- imply
  ((Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (k : Fin m) (j : Fin d) => (-x) ^ ((j : ℤ) - (k : ℕ)) * ((j : ℕ).choose k : ℝ))) i j =
    x ^ (j : ℕ) * Nat.iterate (fwdDiff (1 : ℝ)) j (fun r : ℝ => r ^ (i : ℕ)) δ := by
-- proof
  have hj := j.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) * ((-x) ^ (((j : ℕ) : ℤ) - (k : ℤ)) * ((j : ℕ).choose k : ℝ))) m]
  rw [← Finset.sum_subset (s₁ := Finset.range ((j : ℕ) + 1)) (s₂ := Finset.range m) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [show (((j : ℕ) : ℤ) - (t : ℤ)) = (((j : ℕ) - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ (j : ℕ))]; ring,
    zpow_natCast, neg_pow, show x ^ (j : ℕ) = x ^ t * x ^ ((j : ℕ) - t) by rw [← pow_add]; congr 1; omega,
    zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring


-- created on 2026-10-07
