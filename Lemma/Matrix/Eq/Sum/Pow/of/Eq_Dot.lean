import Lemma.Matrix.GetDot_SwapMatrix.eq.Get
open Matrix


@[path]
private lemma main
  [Semiring α]
  {m : ℕ}
  {x y : Fin n → α}
  {i j : Fin n}
-- given
  (h : x ᵥ* swapMatrix (α := α) i j = y) :
-- imply
  ∑ k : Fin n, x k ^ m = ∑ k : Fin n, y k ^ m := by
-- proof
  have hs : y = x ∘ Equiv.swap i j := by
    rw [← h, GetDot_SwapMatrix.eq.Get]
  rw [hs]
  simp only [Function.comp_apply]
  apply Eq.symm
  apply Equiv.sum_comp (Equiv.swap i j) (fun k : Fin n ↦ x k ^ m)


-- created on 2026-10-31
