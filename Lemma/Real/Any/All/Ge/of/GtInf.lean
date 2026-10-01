import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₁ : BddBelow (f '' S))
  (h : sInf (f '' S) > M₀) :
-- imply
  ∃ M > M₀, ∀ x ∈ S, f x ≥ M := by
-- proof
  refine ⟨sInf (f '' S), h, fun x hx => csInf_le h₁ (Set.mem_image_of_mem f hx)⟩


-- created on 2019-01-05
