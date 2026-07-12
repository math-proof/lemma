import Lemma.Bool.SEqUFnS.of.SEq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B) :
-- imply
  Aᵀ ≃ Bᵀ := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2026-07-12
