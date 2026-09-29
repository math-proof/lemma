import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M : ℝ}
-- given
  (h₀ : BddBelow (f '' S))
  (h : M = sInf (f '' S)) :
-- imply
  ∀ x ∈ S, M ≤ f x := by
-- proof
  intro x hx
  rw [h]
  exact csInf_le h₀ (Set.mem_image_of_mem f hx)


-- created on 2026-09-27
