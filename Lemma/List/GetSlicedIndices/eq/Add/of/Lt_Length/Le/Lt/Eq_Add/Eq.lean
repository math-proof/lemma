import Lemma.List.GetSlicedIndices.eq.Add.of.Lt_Length.Le.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
open List


@[main]
private lemma main
-- given
  (h_j : start = j)
  (h_n : stop = n' + j)
  (h_start : start < stop)
  (h_stop : stop ≤ n + j)
  (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length) :
-- imply
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i + j := by
-- proof
  rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop (by simp)] at h_i
  rw [h_j] at h_start
  rw [h_n] at h_stop h_start
  have h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length := by
    rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop (by simp)]
    simp_all
  have := GetSlicedIndices.eq.Add.of.Lt_Length.Le.Lt h_start h_stop h_i
  simp_all


-- created on 2025-05-24
