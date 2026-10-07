import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import sympy.Basic


@[main]
private lemma main
  {n m d : ℕ}
  {x δ l : ℝ} :
-- imply
  (Matrix.of fun (i : Fin n) (j : Fin m) => x ^ (j : ℕ) * ((j : ℝ) + δ) ^ (i : ℕ)) *
    (Matrix.of fun (i : Fin m) (j : Fin (m - d)) =>
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : ℝ) else 0)) =
    (Matrix.of fun (i j : Fin n) => ((i : ℕ).choose j : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (j : ℕ))) *
    (Matrix.of fun (i : Fin n) (j : Fin (m - d)) => ((j : ℝ) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) := by
-- proof
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : ℝ) + δ) ^ (i : ℕ) *
      ((-l) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : ℝ) else 0))) m,
    Fin.sum_univ_eq_sum_range (fun k => (((i : ℕ).choose k : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : ℝ) + δ) ^ k * x ^ (j : ℕ))) n]
  rw [← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (j + d + 1)) (s₂ := Finset.range m) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk'
      obtain h | h := hk'
      · rw [if_neg (by omega), mul_zero, mul_zero]
      · rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero])]
  rw [← Finset.sum_subset (s₁ := Finset.range ((i : ℕ) + 1)) (s₂ := Finset.range n) (by intro k hk; simp at hk ⊢; omega) (by
      intro k _ hk'
      simp only [Finset.mem_range, not_lt] at hk'
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul])]
  rw [Finset.sum_Ico_eq_sum_range, show (j : ℕ) + d + 1 - j = d + 1 by omega]
  have R : ∀ k ∈ Finset.range ((i : ℕ) + 1), (((i : ℕ).choose k : ℝ) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h * (h : ℝ) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : ℝ) + δ) ^ k * x ^ (j : ℕ)) =
      ∑ h ∈ Finset.range (d + 1), x ^ (j : ℕ) * ((d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h *
        ((((j : ℕ) : ℝ) + δ) ^ k * (h : ℝ) ^ ((i : ℕ) - k) * ((i : ℕ).choose k : ℝ))) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show ((i : ℤ) - (k : ℤ)) = (((i : ℕ) - k : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : k ≤ (i : ℕ))]; ring,
      zpow_natCast]
    ring
  rw [Finset.sum_congr rfl R, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_pow, if_pos (by omega), Nat.add_sub_cancel_left,
    show ((d : ℤ) + ((j : ℕ) : ℤ) - (((j : ℕ) + t : ℕ) : ℤ)) = ((d - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ d)]; ring,
    zpow_natCast, pow_add]
  push_cast
  ring


-- created on 2026-10-07
