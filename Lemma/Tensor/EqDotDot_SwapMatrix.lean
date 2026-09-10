import Lemma.Tensor.GetDot_SwapMatrix.eq.Get
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  (x @ SwapMatrix (α := α) n i j) @ SwapMatrix (α := α) n i j = x := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro
  apply (GetDot_SwapMatrix.eq.Get _ _ _ _).trans
  apply (GetDot_SwapMatrix.eq.Get _ _ _ _).trans
  rw [Equiv.swap_apply_self]
  rfl


-- created on 2026-09-10
