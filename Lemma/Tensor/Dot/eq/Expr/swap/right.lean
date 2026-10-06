import sympy.matrices.expressions.permutation
import sympy.vector.Basic
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.GetDot_SwapMatrix.eq.Get
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  let P : Tensor α [n, n] := SwapMatrix n i j
  (x @ P) @ P = x := by
-- proof
  intro P
  simp only [P]
  apply Eq.of.All_EqGetS.fin
  intro k
  apply Eq.trans (GetDot_SwapMatrix.eq.Get (x @ SwapMatrix (α := α) n i j) i j k)
  apply Eq.trans (GetDot_SwapMatrix.eq.Get x i j (Equiv.swap i j k))
  rw [Equiv.swap_apply_self]
  rfl


-- created on 2020-11-15
-- updated on 2022-10-11
