import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
open List


@[main]
private lemma main
-- given
  (h_start : j < n + j)
  (h_stop : n + j ≤ n' + j) :
-- imply
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length = n := by
-- proof
  
  simp [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]


-- created on 2025-11-09
