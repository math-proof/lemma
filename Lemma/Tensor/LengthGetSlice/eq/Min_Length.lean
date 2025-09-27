import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthGetSlice.eq.Min
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  X[:n].length = n ⊓ X.length := by
-- proof
  match s with
  | [] =>
    simp [Tensor.length]
    simp [Slice.length]
  | s₀ :: s =>
    rw [LengthGetSlice.eq.Min]
    rw [Length.eq.Get_0.of.GtLength_0 (by simp)]
    simp


-- created on 2025-08-04
