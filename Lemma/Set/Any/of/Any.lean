import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.swap
  {f g : ℝ → ℤ}
-- given
  (h : ∃ e, g e > 0 ∧ f e > 0) :
-- imply
  ∃ e, f e > 0 ∧ g e > 0 := by
-- proof
  obtain ⟨e, h1, h2⟩ := h
  exact ⟨e, h2, h1⟩


-- created on 2026-09-27
