import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic


@[path]
private lemma main
  {d m : ℕ}
  {x δ : ℝ} :
-- imply
  (Matrix.of fun (i : Fin d) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-x) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) = 0 := by
-- proof
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) *
      ((-x) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : ℝ) else 0))) m]
  rw [← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (j + d + 1)) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk'
      obtain h | h := hk'
      · rw [if_neg (by omega), mul_zero, mul_zero]
      · rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [Finset.sum_Ico_eq_sum_range, show (j : ℕ) + d + 1 - j = d + 1 by omega]
  have key : ∀ t ∈ Finset.range (d + 1), x ^ ((j : ℕ) + t) * ((((j : ℕ) + t : ℕ) : ℝ) + δ) ^ (i : ℕ) *
      ((-x) ^ ((d : ℤ) + (j : ℕ) - (((j : ℕ) + t : ℕ) : ℤ)) * (if (j : ℕ) ≤ (j : ℕ) + t then (d.choose ((j : ℕ) + t - j) : ℝ) else 0)) =
      x ^ ((j : ℕ) + d) * (((-1 : ℤ) ^ (d - t) * ((d.choose t : ℕ) : ℤ)) • (fun r : ℝ => r ^ (i : ℕ)) (((j : ℝ) + δ) + t • (1 : ℝ))) := by
    intro t ht
    have ht := Finset.mem_range.mp ht
    rw [if_pos (by omega), Nat.add_sub_cancel_left,
      show ((d : ℤ) + ((j : ℕ) : ℤ) - (((j : ℕ) + t : ℕ) : ℤ)) = ((d - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ d)]; ring,
      zpow_natCast, neg_pow, show x ^ ((j : ℕ) + d) = x ^ ((j : ℕ) + t) * x ^ (d - t) by rw [← pow_add]; congr 1; omega,
      zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum,
    ← fwdDiff_iter_eq_sum_shift (h := (1 : ℝ)) (fun r : ℝ => r ^ (i : ℕ)) d ((j : ℝ) + δ),
    fwdDiff_iter_pow_eq_zero_of_lt (by omega : (i : ℕ) < d), Pi.zero_apply, mul_zero]


-- created on 2026-10-07
