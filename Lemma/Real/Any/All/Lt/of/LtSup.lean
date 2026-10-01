import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : sSup (f '' S) < M₀) :
-- imply
  ∃ M < M₀, ∀ x ∈ S, f x < M := by
-- proof
  refine ⟨(sSup (f '' S) + M₀) / 2, by linarith, fun x hx => ?_⟩
  have := le_csSup h₀ (Set.mem_image_of_mem f hx)
  linarith


-- created on 2018-12-28
