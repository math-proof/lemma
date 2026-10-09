import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : M = sSup (f '' S)) :
-- imply
  ∀ x ∈ S, f x ≤ M := by
-- proof
  intro x hx
  rw [h]
  exact le_csSup h₀ (Set.mem_image_of_mem f hx)


-- created on 2018-12-28
