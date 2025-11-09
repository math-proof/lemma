import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.Ne_0.of.Gt
open List Nat


@[main]
private lemma main
-- given
  (h_start : j < n * d + j)
  (h_stop : n * d + j ≤ n' * d + j)
  (h_step : d > 0) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step).length = n := by
-- proof
  have := Ne_0.of.Gt h_step
  simp_all [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]


-- created on 2025-11-09
