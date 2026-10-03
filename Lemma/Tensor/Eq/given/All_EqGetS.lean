import Lemma.Tensor.Eq.is.All_EqGetS
import sympy.Basic
open Tensor


@[main]
private lemma main
  {A B : Tensor α (m :: s)}
-- given
  (h : ∀ i : Fin m, A[i] = B[i]) :
-- imply
  A = B := by
-- proof
  exact Eq.of.All_EqGetS h


-- created on 2026-10-03
