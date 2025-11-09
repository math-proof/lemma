import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.List.EqLengthGetSlicedIndices.of.LeAddS.Lt_Add
open List


private lemma lt_length
-- given
  (h_start : j < n + j)
  (h_stop : n + j ≤ n' + j)
  (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length) :
-- imply
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i + j := by
-- proof
  rw [EqLengthGetSlicedIndices.of.LeAddS.Lt_Add h_start h_stop] at h_i
  have h_start : j < n * 1 + j := by
    simp
    linarith
  have h_stop : n * 1 + j ≤ n' * 1 + j := by
    simp
    linarith
  have h_step : 1 > 0 := by
    simp
  have := GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul h_start h_stop h_step h_i
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


@[main]
private lemma main
-- given
  (h_start : j < n + j)
  (h_stop : n + j ≤ n' + j)
  (h_i : i < n) :
-- imply
  have := EqLengthGetSlicedIndices.of.LeAddS.Lt_Add h_start h_stop
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i]'(by rwa [this]) = i + j := by
-- proof
  apply lt_length


-- created on 2025-05-24
-- updated on 2025-11-09
