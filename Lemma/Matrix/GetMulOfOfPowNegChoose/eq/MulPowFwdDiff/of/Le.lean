import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Syntax.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Field R]
  {d m : ℕ}
  {x δ : R}
-- given
  (h : d ≤ m)
  (i j : Fin d) :
-- imply
  (([i < d, j < m] (x ^ (j : ℕ) * ((j : R) + δ) ^ (i : ℕ))) *
    ([k < m, j < d] ((-x) ^ (j - k : ℤ) * ((j : ℕ).choose k : R)))) i j =
    x ^ (j : ℕ) * Nat.iterate (fwdDiff (1 : R)) j (fun r : R => r ^ (i : ℕ)) δ := by
-- proof
  unfold Matrix.ofFun
  have hj := j.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : R) + δ) ^ (i : ℕ) * ((-x) ^ (((j : ℕ) : ℤ) - (k : ℤ)) * ((j : ℕ).choose k : R))) m]
  have hzero (k : ℕ) (hk : k ∈ Finset.range m) (hk' : k ∉ Finset.range ((j : ℕ) + 1)) :
    x ^ k * ((k : R) + δ) ^ (i : ℕ) *
      ((-x) ^ (((j : ℕ) : ℤ) - (k : ℤ)) * ((j : ℕ).choose k : R)) = 0 := by
        simp only [Finset.mem_range, not_lt] at hk'
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
  rw [← Finset.sum_subset (s₁ := Finset.range ((j : ℕ) + 1)) (s₂ := Finset.range m)
      (by intro k hk; simp at hk ⊢; omega) hzero]
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [show (((j : ℕ) : ℤ) - (t : ℤ)) = (((j : ℕ) - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ (j : ℕ))]; ring,
    zpow_natCast, neg_pow, show x ^ (j : ℕ) = x ^ t * x ^ ((j : ℕ) - t) by rw [← pow_add]; congr 1; omega,
    zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring


-- created on 2026-10-07
-- updated on 2026-10-26
