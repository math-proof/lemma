import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
open Matrix


@[path]
private lemma main
  [Semiring α] [DecidableEq α]
  {x y : Fin n → α}
  {i j : Fin n}
-- given
  (h : y = x ᵥ* swapMatrix (α := α) i j) :
-- imply
  Finset.univ.image y = Finset.univ.image x := by
-- proof
  have hs : y = x ∘ Equiv.swap i j := by
    rw [h, GetDot_SwapMatrix.eq.Get]
  rw [hs, ← Finset.image_image, Finset.image_univ_equiv]


-- created on 2026-10-31
