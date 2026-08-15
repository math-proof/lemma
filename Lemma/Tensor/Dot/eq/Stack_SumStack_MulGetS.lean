import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetDot.eq.SumStack_MulGetS
open Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [i < m] [j < n] ∑ k < l, (let a : Tensor α [] := A[i][k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fn.fin (i := i)]
  conv_rhs => erw [EqGetStack.fn.fin (i := j)]
  simp [GetElem.getElem]
  apply GetDot.eq.SumStack_MulGetS.fin


@[main, fin]
private lemma une
  [Mul α] [Add α] [Zero α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [j < n] ∑ k < l, (let a : Tensor α [] := A[k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fn.fin (i := j)]
  simp [GetElem.getElem]
  apply GetDot.eq.SumStack_MulGetS.une.fin


-- created on 2026-08-14
