import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α (n :: s)) :
-- imply
  [i < n] X[i] = X := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  rfl


-- created on 2025-11-11
