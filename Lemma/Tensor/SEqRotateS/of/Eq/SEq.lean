import Lemma.Bool.SEqBFnS.of.SEq
import sympy.tensor.Basic
open Bool


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (h_i : i = i') :
-- imply
  A.rotate i ≃ B.rotate i' := by
-- proof
  subst h_i
  apply SEqBFnS.of.SEq h


-- created on 2025-10-19
