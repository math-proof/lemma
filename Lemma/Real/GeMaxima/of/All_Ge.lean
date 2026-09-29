import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {m : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h : ∀ x ∈ S, f x ≥ m) :
-- imply
  Maxima S f ≥ m := by
-- proof
  obtain ⟨x, hx⟩ := h₀
  exact le_trans (h x hx) (le_csSup h₁ (Set.mem_image_of_mem f hx))


-- created on 2026-09-27
