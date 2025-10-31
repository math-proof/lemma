import Lemma.Tensor.SEqSoftmaxS.of.SEq
import sympy.tensor.functions
open Tensor


@[main]
private lemma main
  [Exp α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i = i')
  (h : A ≃ B) :
-- imply
  A.softmax i ≃ B.softmax i' := by
-- proof
  subst h_i
  apply SEqSoftmaxS.of.SEq h


-- created on 2025-10-31
