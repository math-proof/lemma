import Lemma.List.GetSlicedIndices.eq.Add.of.Lt_Length.Le.Lt.Eq_Add.Eq
open List


@[main]
private lemma main
-- given
  (h₀ : start = 0)
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length) :
-- imply
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i := by
-- proof
  have h_all : ∀ (j : ℕ) (n' : ℕ) (h₀ : start = j) (h_n : stop = n' + j) (h_start : start < stop) (h_stop : stop ≤ n + j) (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length), (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i + j := by
    intro j n' h₀ h_n h_start h_stop h_i
    exact GetSlicedIndices.eq.Add.of.Lt_Length.Le.Lt.Eq_Add.Eq h₀ h_n h_start h_stop h_i
  apply h_all 0 stop h₀ rfl h_start h_stop h_i


-- created on 2025-08-04
