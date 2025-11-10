import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
import Lemma.Nat.Mul
import stdlib.Slice
open List Rat Nat


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


@[main]
private lemma Comm
-- given
  (h_j : j < d)
  (h_n : n > 0)
  (h_step : d > 0) :
-- imply
  (Nat.sliced_indices (n := d * n) (start := j) (stop := d * n) (by nlinarith) (by simp) h_step).length = n := by
-- proof
  simp [LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt]
  rw [Mul.comm]
  rwa [EqToNatCeilDivSubMul.of.Lt]


-- created on 2025-11-09
