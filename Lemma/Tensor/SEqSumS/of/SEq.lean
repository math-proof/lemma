import Lemma.Bool.SEqBFnS.of.SEq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  [Add α] [Zero α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.sum i ≃ B.sum i := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-06-29
-- updated on 2025-07-13
