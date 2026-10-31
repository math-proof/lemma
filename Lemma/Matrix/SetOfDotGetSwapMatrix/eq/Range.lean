import Lemma.Matrix.DotGetSwapMatrix.eq.Get
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  Set.range (swapMatrix i j *ᵥ x) = Set.range x := by
-- proof
  rw [DotGetSwapMatrix.eq.Get]
  apply (Equiv.swap i j).surjective.range_comp


-- created on 2026-10-31
