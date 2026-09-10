import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetT
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α [m, n]) :
-- imply
  Xᵀᵀ = X := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [EqGetT.fin]
  conv_lhs => erw [EqGetT.fin]
  rfl


-- created on 2026-07-21
