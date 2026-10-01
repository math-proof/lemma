import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : ∀ M < M₀, ∃ x ∈ S, f x > M) :
-- imply
  sSup (f '' S) ≥ M₀ := by
-- proof
  apply le_of_forall_lt
  intro c hc
  obtain ⟨x, hx, hfx⟩ := h c hc
  exact lt_of_lt_of_le hfx (le_csSup h₀ (Set.mem_image_of_mem f hx))


@[main]
private lemma main
  {S : Set ℝ}
  {f : ℝ → ℝ}
  {M₀ : ℝ}
-- given
  (h₀ : BddAbove (f '' S))
  (h : ∀ M < M₀, ∃ x ∈ S, f x > M) :
-- imply
  sSup (f '' S) ≥ M₀ := by
-- proof
  apply le_of_forall_lt
  intro c hc
  obtain ⟨x, hx, hfx⟩ := h c hc
  exact lt_of_lt_of_le hfx (le_csSup h₀ (Set.mem_image_of_mem f hx))


-- created on 2019-04-11
