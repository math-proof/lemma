import Lemma.Matrix.DotGetSwapMatrix.eq.Get
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  let P := swapMatrix (α := α) i j
  (P * P) *ᵥ x = x := by
-- proof
  intro P
  simp only [P]
  rw [← mulVec_mulVec, DotGetSwapMatrix.eq.Get, DotGetSwapMatrix.eq.Get]
  funext k
  simp [Equiv.swap_apply_self]


-- created on 2026-10-31
