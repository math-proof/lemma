import sympy.tensor.Basic
import Lemma.Tensor.SEqPermuteTailS.of.SEq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_i : i = i')
  (h : A ≃ B) :
-- imply
  A.permuteTail i ≃ B.permuteTail i' := by
-- proof
  subst h_i
  apply SEqPermuteTailS.of.SEq h


-- created on 2025-10-26
