import Lemma.Tensor.Dot
import Notation.Data.Tensor.Permute
import Lemma.Tensor.EqTT
import Lemma.Tensor.GetDot.eq.DotGetS
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  [CommMagma α] [Add α] [Zero α]
-- given
  (X : Tensor α [m, k])
  (Y : Tensor α [k, n]) :
-- imply
  (X ⬝ᵥ Y)ᵀ = Yᵀ ⬝ᵥ Xᵀ := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [EqGetT.fin]
  conv_lhs => erw [GetDot.eq.DotGetS.fin]
  conv_rhs => erw [GetDot.eq.DotGetS.fin]
  conv_rhs =>
    arg 2
    erw [EqTT]
  apply Dot.comm


-- created on 2026-07-21
