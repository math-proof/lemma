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
  (h : M = Maxima S f) :
-- imply
  ∀ x ∈ S, M ≥ f x := by
-- proof
  intro x hx
  rw [h]
  exact le_csSup h₀ (Set.mem_image_of_mem f hx)


-- created on 2019-01-14
