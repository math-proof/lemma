import Lemma.Tensor.Dot
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqTT
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.GetDot.eq.DotGetS
import Lemma.Tensor.TDot.eq.DotTS
open Tensor


@[main]
private lemma main
  [CommMagma α] [Add α] [Zero α]
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
  conv_lhs => erw [TDot.eq.DotTS]
  apply Eq.of.All_EqGetS.fin
  intro k
  conv_lhs => erw [GetDot.eq.DotGetS.fin]
  conv_lhs =>
    arg 2
    erw [EqTT]
  conv_rhs => erw [GetDot.eq.DotGet.une.fin]
  apply Dot.comm


-- created on 2026-07-09
-- updated on 2026-07-21
