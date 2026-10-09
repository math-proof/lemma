import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : sSup (f '' S) < M₀) :
-- imply
  ∃ M < M₀, ∀ x ∈ S, f x ≤ M := by
-- proof
  exact ⟨sSup (f '' S), h, fun x hx => le_csSup h₀ (Set.mem_image_of_mem f hx)⟩


-- created on 2018-12-29
