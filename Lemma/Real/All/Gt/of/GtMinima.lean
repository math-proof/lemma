import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₁ : BddBelow (f '' S))
  (h : Minima S f > M) :
-- imply
  ∀ x ∈ S, f x > M := by
-- proof
  intro x hx
  exact lt_of_lt_of_le h (csInf_le h₁ (Set.mem_image_of_mem f hx))


-- created on 2023-11-12
