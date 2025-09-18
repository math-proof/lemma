import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
open Tensor


@[main]
private lemma main
  [Mul α]
  [AddCommMonoid α]
-- given
  (A : Tensor α [m, l])
  (B : Tensor α [l, n]) :
-- imply
  A @ B = [i < m] [j < n] ∑ k : Fin l, A[i, k] * B[k, j] := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  apply Eq.of.All_EqGetS
  intro j
  repeat rw [EqGetStack.fn]
  apply GetDot.eq.Sum_MulGetS


-- created on 2025-07-19
