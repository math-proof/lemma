import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set α}
  {f : α → ℝ}
  {M : ℝ}
-- given
  (_h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h : sSup (f '' S) ≤ M) :
-- imply
  ∀ x ∈ S, f x ≤ M := by
-- proof
  intro x hx
  exact le_trans (le_csSup h₁ (Set.mem_image_of_mem f hx)) h


-- created on 2019-04-10
