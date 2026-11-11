import Notation.Data.Tensor.Permute
import Lemma.Tensor.GetDot.eq.DotGetS
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A ⬝ᵥ B = [i < m] [j < n] A[i] ⬝ᵥ Bᵀ[j] := by
-- proof
  simp [GetElem.getElem]
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fin (i := i)]
  conv_rhs => erw [EqGetStack.fin (i := j)]
  apply GetDot.eq.DotGetS.fin


-- created on 2025-07-19
-- updated on 2026-10-26
