import Lemma.Bool.SEqBFnS.of.SEq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  [Neg α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  -X ≃ -Y := by
-- proof
  apply SEqBFnS.of.SEq h


-- created on 2025-12-04
