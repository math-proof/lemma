import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  [i < n] X[i.val] = X := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  rfl


-- created on 2025-11-11
