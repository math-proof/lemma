import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₁ : BddBelow (f '' S)) :
-- imply
  ∀ x ∈ S, f x ≥ Minima S f := by
-- proof
  intro x hx
  exact csInf_le h₁ (Set.mem_image_of_mem f hx)


-- created on 2026-09-27
