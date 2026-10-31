import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  (x ᵥ* swapMatrix (α := α) i j) ᵥ* swapMatrix (α := α) i j = x := by
-- proof
  rw [GetDot_SwapMatrix.eq.Get, GetDot_SwapMatrix.eq.Get]
  funext k
  simp [Equiv.swap_apply_self]


-- created on 2026-10-31
