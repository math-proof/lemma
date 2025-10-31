import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.GtLength_Add
import stdlib.SEq
import sympy.tensor.functions
open List


@[main]
private lemma main
  [Add α] [Zero α]
  {i d : ℕ}
-- given
  (h : s.length > i + d)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by grind⟩ d).sum (i + d) ≃ X.sum i := by
-- proof
  constructor
  .
    apply EraseIdxPermute.eq.EraseIdx.of.GtLength_Add h
  .
    sorry


-- created on 2025-10-31
