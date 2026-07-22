import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetDot.eq.DotGetS
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [i < m] [j < n] A[i] @ Bᵀ[j] := by
-- proof
  simp [GetElem.getElem]
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fn.fin (i := i)]
  conv_rhs => erw [EqGetStack.fn.fin (i := j)]
  apply GetDot.eq.DotGetS.fin


-- created on 2025-07-19
-- updated on 2026-07-21
