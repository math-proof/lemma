import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {M : ℝ}
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : Maxima S f ≤ M) :
-- imply
  ∀ x ∈ S, f x ≤ M := by
-- proof
  exact fun x hx => le_trans (le_csSup h₀ (Set.mem_image_of_mem f hx)) h


-- created on 2026-09-27
