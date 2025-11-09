import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
import stdlib.Slice
open List Rat


@[main]
private lemma main
-- given
  (h_j : j < d)
  (h_n : n > 0)
  (h_step : d > 0) :
-- imply
  (Nat.sliced_indices (n := n * d) (start := j) (stop := n * d) (by nlinarith) (by simp) h_step).length = n := by
-- proof
  simp [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]
  rwa [EqToNatCeilDivSubMul.of.Lt]


-- created on 2025-11-09
