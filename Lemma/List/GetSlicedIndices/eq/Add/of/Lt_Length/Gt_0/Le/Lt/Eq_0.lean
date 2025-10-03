import Lemma.List.GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_Add.Eq
open List


@[main]
private lemma main
-- given
  (h₀ : start = 0)
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : 1 > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = i := by
-- proof
  have h_all : ∀ (j : ℕ) (n' : ℕ) (h₀ : start = j) (h_n : stop = n' + j) (h_start : start < stop) (h_stop : stop ≤ n + j) (h_step : 1 > 0) (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length), (Nat.sliced_indices h_start h_stop h_step)[i] = i + j := by
    intro j n' h₀ h_n h_start h_stop h_step h_i
    exact GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_Add.Eq h₀ h_n h_start h_stop h_step h_i
  apply h_all 0 stop h₀ rfl h_start h_stop h_step h_i


-- created on 2025-08-04
