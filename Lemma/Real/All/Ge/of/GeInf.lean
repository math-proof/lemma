import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {y : ℝ}
-- given
  (h₀ : BddBelow (f '' S))
  (h : sInf (f '' S) ≥ y) :
-- imply
  ∀ x ∈ S, f x ≥ y := by
-- proof
  intro x hx
  exact le_trans h (csInf_le h₀ (Set.mem_image_of_mem f hx))


-- created on 2019-04-06
