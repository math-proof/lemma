import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Dot
import Lemma.Tensor.GetDot.eq.DotGet
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.DotT.eq.Dot
import sympy.tensor.tensor
open Bool Tensor


@[main, fin]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n])
  (X : Tensor α [n, m])
  (j : Fin m) :
-- imply
  (A @ X)[j]'(by grind [matmul_shape]) = A @ Xᵀ[j] := by
-- proof
  simp [GetElem.getElem]
  have h_dot := GetDot.eq.DotGet.une.fin Xᵀ A j
  simp at h_dot
  have h_dot := h_dot.trans (Dot.comm (Xᵀ.get j) A)
  symm at h_dot ⊢
  apply h_dot.trans
  apply Eq.of.SEq
  apply SEqGetS.of.SEq.GtLength
  apply SEq.of.Eq
  apply DotT.eq.Dot


-- created on 2026-07-30
