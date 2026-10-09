import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : BddAbove (f '' S)) :
-- imply
  ∀ x ∈ S, Maxima S f ≥ f x := by
-- proof
  exact fun x hx => le_csSup h₀ (Set.mem_image_of_mem f hx)


-- created on 2019-09-16
