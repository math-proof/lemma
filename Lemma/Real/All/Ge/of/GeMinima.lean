import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : BddBelow (f '' S))
  (h : Minima S f ≥ M) :
-- imply
  ∀ x ∈ S, f x ≥ M := by
-- proof
  intro x hx
  exact le_trans h (csInf_le h₀ (Set.mem_image_of_mem f hx))


-- created on 2026-09-27
