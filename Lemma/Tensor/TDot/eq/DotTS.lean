import Lemma.Tensor.Dot
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqTT
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetTranspose.eq.Get
open Tensor


@[main]
private lemma main
  [CommMagma α] [Add α] [Zero α]
-- given
  (X : Tensor α [m, k])
  (Y : Tensor α [k, n]) :
-- imply
  (X @ Y)ᵀ = Yᵀ @ Xᵀ := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [GetTranspose.eq.Get.fin]
  conv_lhs => erw [GetDot.eq.DotGetS.fin]
  conv_rhs => erw [GetDot.eq.DotGetS.fin]
  conv_rhs =>
    arg 2
    erw [EqTT]
  apply Dot.comm


-- created on 2026-07-21
