import Lemma.List.GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.MulToNatCeilDivSub.in.Ico
open List Nat Slice


@[main]
private lemma main
  {start stop N step i : ℕ}
-- given
  (h_start : start < stop)
  (h_stop : stop ≤ N)
  (h_step : step > 0)
  (h_i : i < (Nat.sliced_indices h_start h_stop h_step).length) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step)[i] < stop := by
-- proof
  rw [GetSlicedIndices.eq.AddMul.of.GtLength.Gt_0.Le.Lt h_start h_stop h_step h_i]
  rw [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step] at h_i
  calc
    _ < start + (stop - start) := by grind [MulToNatCeilDivSub.in.Ico h_start h_step, Nat.mul_le_mul_right step (Nat.succ_le_of_lt h_i)]
    _ = stop := by grind


-- created on 2026-08-09
