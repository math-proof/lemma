import Lemma.List.EqLengthGetSlicedIndices.of.Gt_0.LeAddMul.Lt_AddMul
import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul
open List


@[main]
private lemma main
-- given
  (h_n : n > 0)
  (h_step : d > 0)
  (h_i : i < n) :
-- imply
  have := EqLengthGetSlicedIndices.of.Gt_0.LeAddMul.Lt_AddMul (j := j) (n := n) (N := n * d + j) (by simp [And.intro h_n h_step]) (by simp) h_step
  (Nat.sliced_indices (start := j) (stop := n * d + j) (n := n * d + j) (by simp [And.intro h_n h_step]) (by simp) h_step)[i]'(by rwa [this]) = i * d + j := by
-- proof
  rw [← GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul _ _ _ h_i]


-- created on 2025-11-09
