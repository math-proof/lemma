import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₁ : BddBelow (f '' S))
  (h : sInf (f '' S) > M₀) :
-- imply
  ∃ M > M₀, ∀ x ∈ S, f x > M := by
-- proof
  refine ⟨(sInf (f '' S) + M₀) / 2, by linarith, fun x hx => ?_⟩
  have := csInf_le h₁ (Set.mem_image_of_mem f hx)
  linarith


-- created on 2019-01-05
