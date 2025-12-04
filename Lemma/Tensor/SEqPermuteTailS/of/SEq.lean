import Lemma.Bool.SEqBFnS.of.SEq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.permuteTail i ≃ B.permuteTail i := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-10-26
