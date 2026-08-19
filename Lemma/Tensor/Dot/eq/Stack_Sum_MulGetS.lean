import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
open Tensor


@[main, fin]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [i < m] [j < n] ∑ k : Fin l, id (α := Tensor α []) A[i][k] * id (α := Tensor α []) B[k][j] := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fin (i := i)]
  conv_rhs => erw [EqGetStack.fin (i := j)]
  simp [GetElem.getElem]
  apply GetDot.eq.Sum_MulGetS.fin


@[main, fin]
private lemma une
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [j < n] ∑ k : Fin l, id (α := Tensor α []) A[k] * id (α := Tensor α []) B[k][j] := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fin (i := j)]
  simp [GetElem.getElem]
  apply GetDot.eq.Sum_MulGetS.une.fin


-- created on 2018-04-02
-- updated on 2026-08-19
