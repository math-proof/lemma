import Lemma.Tensor.SumDiv.eq.DivSum.of.Lt_Length
import Lemma.Tensor.SumDiv.eq.DivSum.of.Ge_Length
open Tensor


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (X : Tensor α s)
  (n : Tensor α [])
  (dim : ℕ) :
-- imply
  (X / n).sum dim = X.sum dim / n := by
-- proof
  if h : dim < s.length then
    apply SumDiv.eq.DivSum.of.Lt_Length h
  else
    simp at h
    apply SumDiv.eq.DivSum.of.Ge_Length h


-- created on 2025-09-21
-- updated on 2025-09-25
