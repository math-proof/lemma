import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₁ : BddAbove (f '' S))
  (h : sSup (f '' S) < M) :
-- imply
  ∀ x ∈ S, f x < M := by
-- proof
  intro x hx
  exact lt_of_le_of_lt (le_csSup h₁ (Set.mem_image_of_mem f hx)) h


-- created on 2020-01-15
