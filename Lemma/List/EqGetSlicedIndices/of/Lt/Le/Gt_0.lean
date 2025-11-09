import Lemma.List.EqLengthGetSlicedIndices.of.LeAddS.Lt_Add
import Lemma.List.EqLengthSlicedIndices.of.Le.Gt_0
import Lemma.List.GetSlicedIndices.eq.Add.of.Lt.LeAddS.Lt_Add
open List


@[main]
private lemma main
-- given
  (h_start : 0 < stop)
  (h_stop : stop ≤ n)
  (h_i : i < stop) :
-- imply
  have := EqLengthSlicedIndices.of.Le.Gt_0 (by simp_all) h_stop
  (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i]'(by simp_all) = i := by
-- proof
  have h_all : ∀ (h_start : 0 < stop) (h_stop : stop ≤ n) (h_i : i < (Nat.sliced_indices (step := 1) h_start h_stop (by simp)).length), (Nat.sliced_indices (step := 1) h_start h_stop (by simp))[i] = i := by
    intro h_start h_stop h_i
    apply GetSlicedIndices.eq.Add.of.Lt.LeAddS.Lt_Add
    rwa [EqLengthGetSlicedIndices.of.LeAddS.Lt_Add] at h_i
  apply h_all h_start h_stop


-- created on 2025-08-04
-- updated on 2025-11-09
