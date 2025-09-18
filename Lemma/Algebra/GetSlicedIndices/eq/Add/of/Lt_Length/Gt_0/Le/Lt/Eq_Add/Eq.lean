import Lemma.Algebra.GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt
import Lemma.Algebra.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
open Algebra


@[main]
private lemma main
-- given
  (h_j : start = j)
  (h_n : stop = n' + j)
  (h_start : start < stop)
  (h_stop : stop ≤ n + j)
  (h_step : 1 > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] = i + j := by
-- proof
  rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step] at h_i
  rw [h_j] at h_start
  rw [h_n] at h_stop h_start
  have h_i : i < (Nat.sliced_indices h_start h_stop h_step).length := by
    rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step]
    simp_all
  have := GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt h_start h_stop h_step h_i
  simp_all


-- created on 2025-05-24
