import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt_Length.Gt_0.LeAddSMul.Lt_AddMul
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
open List


@[main]
private lemma main
-- given
  (h_start : j < n + j)
  (h_stop : n + j ≤ n' + j)
  (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length) :
-- imply
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i + j := by
-- proof
  have h_start : j < n * 1 + j := by 
    simp
    linarith
  have h_stop : n * 1 + j ≤ n' * 1 + j := by 
    simp
    linarith
  have h_step : 1 > 0 := by 
    simp
  have h_i : i < (Nat.sliced_indices h_start h_stop h_step).length := by 
    rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt] at ⊢ h_i
    simp_all
  have := GetSlicedIndices.eq.AddMul.of.Lt_Length.Gt_0.LeAddSMul.Lt_AddMul h_start h_stop h_step h_i
  simp at this
  simp [← this]
  congr
  ·
    grind
  ·
    grind
  ·
    grind
  ·
    rw [show n' * 1 = n' by simp]
  ·
    grind
  ·
    grind
  ·
    grind
  ·
    grind


-- created on 2025-05-24
-- updated on 2025-11-09
