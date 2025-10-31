import Lemma.List.EraseIdxPermute__Neg.eq.EraseIdx.of.Ge
import stdlib.SEq
import sympy.tensor.functions
open List


@[main]
private lemma main
  [Add α] [Zero α]
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : i ≥ d)
  (X : Tensor α s) :
-- imply
  (X.permute i (-d)).sum (i - d) ≃ X.sum i := by
-- proof
  constructor
  ·
    apply EraseIdxPermute__Neg.eq.EraseIdx.of.Ge h
  ·
    sorry


-- created on 2025-10-31
