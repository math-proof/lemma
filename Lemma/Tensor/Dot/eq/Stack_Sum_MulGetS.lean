import Lemma.Tensor.GetDot.eq.Sum_MulGetS
open Tensor


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [i < m] [j < n] ∑ k : Fin l, (let a : Tensor α [] := A[i][k]; a) * (let b : Tensor α [] := B[k][j]; b) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_rhs => erw [EqGetStack.fn.fin (i := i)]
  conv_rhs => erw [EqGetStack.fn.fin (i := j)]
  simp [GetElem.getElem]
  apply GetDot.eq.Sum_MulGetS.fin


-- created on 2025-07-19
