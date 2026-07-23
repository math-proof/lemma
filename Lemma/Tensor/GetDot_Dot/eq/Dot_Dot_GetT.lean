import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Dot
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.GtGet_0.GtLength_0
import Lemma.Tensor.GetT.eq.Select
open Bool Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (L : Tensor α [l, m])
  (M : Tensor α [m, n])
  (N : Tensor α [n, o])
  (i : Fin l)
  (j : Fin o) :
-- imply
  (L @ (M @ N))[i, j] = L[i] @ (M @ Nᵀ[j]) := by
-- proof
  simp [GetElem.getElem]
  erw [GetDot.eq.DotGetS.fin]
  congr 1
  conv_lhs => erw [GetT.eq.Select]
  apply Eq.of.All_EqGetS.fin
  intro k
  conv_lhs => erw [GetSelect_1.eq.Cast_Get.of.Lt.GtGet_0.GtLength_0 (by grind) (by grind) (by grind)]
  apply EqCast.of.SEq
  conv_lhs => erw [GetDot.eq.DotGetS.fin]
  conv_rhs => erw [GetDot.eq.DotGet.une.fin]
  rfl


-- created on 2026-07-09
-- updated on 2026-07-21
