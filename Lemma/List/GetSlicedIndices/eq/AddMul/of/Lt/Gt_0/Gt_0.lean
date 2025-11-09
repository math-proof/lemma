import Lemma.List.EqLengthGetSlicedIndices.of.Gt_0.LeAddSMul.Lt_AddMul
import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul
open List


@[main]
private lemma main
-- given
  (h_n : n > 0)
  (h_step : d > 0)
  (h_i : i < n) :
-- imply
  have := EqLengthGetSlicedIndices.of.Gt_0.LeAddSMul.Lt_AddMul (j := j) (n := n) (n' := n) (by simp [And.intro h_n h_step]) (by simp) h_step
  (Nat.sliced_indices (start := j) (stop := n * d + j) (n := n * d + j) (by simp [And.intro h_n h_step]) (by simp) h_step)[i]'(by rwa [this]) = i * d + j := by
-- proof
  have h_start : j < n * d + j := by nlinarith
  have h_stop : n * d + j ≤ n * d + j := by linarith
  have h_nonzero : d ≠ 0 := by omega
  have := GetSlicedIndices.eq.AddMul.of.Lt.Gt_0.LeAddSMul.Lt_AddMul h_start h_stop h_step h_i
  simp at this
  rw [← this]


-- created on 2025-11-09
