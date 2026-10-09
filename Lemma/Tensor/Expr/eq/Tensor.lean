import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq_Stack
open Tensor


@[path]
private lemma main
-- given
  (X : Tensor α [4, 3]) :
-- imply
  X = [i < 4] [j < 3] X[i][j] := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  erw [EqGetStack]
  exact Eq_Stack _


-- created on 2022-01-12
