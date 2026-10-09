import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
-- given
  (h₀ : BddBelow (f '' S)) :
-- imply
  ∀ x ∈ S, sInf (f '' S) ≤ f x := by
-- proof
  intro x hx
  exact csInf_le h₀ (Set.mem_image_of_mem f hx)


-- created on 2019-09-17
