import Lemma.List.EqLengthGetSlicedIndices.of.Gt_0.LeAddMul.Lt_AddMul
import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul
open List


@[main]
private lemma main
-- given
  (h_start : j < n * d + j)
  (h_stop : n * d + j ≤ N)
  (h_step : d > 0)
  (h_i : i < n) :
-- imply
  have := EqLengthGetSlicedIndices.of.Gt_0.LeAddMul.Lt_AddMul h_start h_stop h_step
  (Nat.sliced_indices h_start h_stop h_step)[i]'(by rwa [this]) = i * d + j := by
-- proof
  apply GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul (j' := ⟨0, h_step⟩)
  simpa


-- created on 2025-11-09
