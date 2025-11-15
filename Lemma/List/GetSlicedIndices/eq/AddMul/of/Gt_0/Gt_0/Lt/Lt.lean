import Lemma.List.EqLengthSlicedIndices.of.Gt_0.Gt_0.Lt
import Lemma.List.GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul
open List


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h_j : j < d)
  (h_n : n > 0)
  (h_d : d > 0) :
-- imply
  have := EqLengthSlicedIndices.of.Gt_0.Gt_0.Lt h_j h_n h_d
  (Nat.sliced_indices (n := n * d) (start := j) (stop := n * d) (by nlinarith) (by nlinarith) h_d)[i]'(by rwa [this]) = i * d + j := by
-- proof
  have := GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul (i := i) (j := j) (j' := ⟨j, h_j⟩) (n := n) (d := d) (N := n * d) (by simp; nlinarith) (by simp) h_i
  simp_all


@[main]
private lemma comm'
-- given
  (h_i : i < n)
  (h_j : j < d)
  (h_n : n > 0)
  (h_d : d > 0) :
-- imply
  have := EqLengthSlicedIndices.of.Gt_0.Gt_0.Lt.comm h_j h_n h_d
  (Nat.sliced_indices (n := d * n) (start := j) (stop := d * n) (by nlinarith) (by nlinarith) h_d)[i]'(by rwa [this]) = i * d + j := by
-- proof
  have := GetSlicedIndices.eq.AddMul.of.Lt.LeSubAddMul.Lt_SubAddMul (i := i) (j := j) (j' := ⟨j, h_j⟩) (n := n) (d := d) (N := d * n) (by simp; nlinarith) (by grind) h_i
  grind


-- created on 2025-11-07
-- updated on 2025-11-09
