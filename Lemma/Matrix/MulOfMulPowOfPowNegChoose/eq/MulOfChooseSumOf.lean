import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Vandermonde
import Initialize.Tactic.Attr.Basic
import Syntax.LinearAlgebra.Matrix.Notation


@[path]
private lemma main
  [Field R]
  {n m d : ℕ}
  {x δ l : R} :
-- imply
  ([i < n, j < m] x ^ (j : ℕ) * ((j : R) + δ) ^ (i : ℕ)) *
    ([i < m, j < m - d]
      (-l) ^ ((d : ℤ) + (j : ℕ) - (i : ℕ)) * (if (j : ℕ) ≤ i then (d.choose ((i : ℕ) - j) : R) else 0)) =
    ([i < n, j < n] (((i : ℕ).choose j : R) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * x ^ h * (h : R) ^ ((i : ℤ) - (j : ℕ)))) *
    ([i < n, j < m - d] ((j : R) + δ) ^ (i : ℕ) * x ^ (j : ℕ)) := by
-- proof
  ext i j
  have hj := j.isLt
  have hi := i.isLt
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => x ^ k * ((k : R) + δ) ^ (i : ℕ) *
      ((-l) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : R) else 0))) m,
    Fin.sum_univ_eq_sum_range (fun k => (((i : ℕ).choose k : R) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * x ^ h * (h : R) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : R) + δ) ^ k * x ^ (j : ℕ))) n]
  have hzero (k : ℕ) (hk : k ∈ Finset.range m) (hk' : k ∉ Finset.Ico (j : ℕ) (j + d + 1)) :
    x ^ k * ((k : R) + δ) ^ (i : ℕ) *
      ((-l) ^ ((d : ℤ) + (j : ℕ) - (k : ℤ)) * (if (j : ℕ) ≤ k then (d.choose (k - j) : R) else 0)) = 0 := by
        simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk'
        obtain h | h := hk'
        · rw [ite_eq_right (by omega), mul_zero, mul_zero]
        · rw [ite_eq_left (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
  have hzero' (k : ℕ) (hk : k ∈ Finset.range n) (hk' : k ∉ Finset.range ((i : ℕ) + 1)) :
    ((i : ℕ).choose k : R) *
      (∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * x ^ h * (h : R) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : R) + δ) ^ k * x ^ (j : ℕ)) = 0 := by
        simp only [Finset.mem_range, not_lt] at hk'
        rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]
  rw [← Finset.sum_subset (s₁ := Finset.Ico (j : ℕ) (j + d + 1)) (s₂ := Finset.range m)
      (by intro k hk; simp at hk ⊢; omega) hzero]
  rw [← Finset.sum_subset (s₁ := Finset.range ((i : ℕ) + 1)) (s₂ := Finset.range n)
      (by intro k hk; simp at hk ⊢; omega) hzero']
  rw [Finset.sum_Ico_eq_sum_range, show (j : ℕ) + d + 1 - j = d + 1 by omega]
  have hR : ∀ k ∈ Finset.range ((i : ℕ) + 1), (((i : ℕ).choose k : R) *
      ∑ h ∈ Finset.range (d + 1), (d.choose h : R) * (-l) ^ (d - h) * x ^ h * (h : R) ^ ((i : ℤ) - (k : ℤ))) *
      ((((j : ℕ) : R) + δ) ^ k * x ^ (j : ℕ)) =
      ∑ h ∈ Finset.range (d + 1), x ^ (j : ℕ) * ((d.choose h : R) * (-l) ^ (d - h) * x ^ h *
        ((((j : ℕ) : R) + δ) ^ k * (h : R) ^ ((i : ℕ) - k) * ((i : ℕ).choose k : R))) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show ((i : ℤ) - (k : ℤ)) = (((i : ℕ) - k : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : k ≤ (i : ℕ))]; ring,
      zpow_natCast]
    ring
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← add_pow, ite_eq_left (by omega), Nat.add_sub_cancel_left,
    show ((d : ℤ) + ((j : ℕ) : ℤ) - (((j : ℕ) + t : ℕ) : ℤ)) = ((d - t : ℕ) : ℤ) by push_cast [Nat.cast_sub (by omega : t ≤ d)]; ring,
    zpow_natCast, pow_add]
  push_cast
  ring


-- created on 2026-10-07
-- updated on 2026-10-27
