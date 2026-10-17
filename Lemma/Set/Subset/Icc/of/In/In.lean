import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : x ∈ Set.Icc a b)
  (h₁ : y ∈ Set.Icc a b) :
-- imply
  Set.Icc (min x y) (max x y) ⊆ Set.Icc a b := by
-- proof
  intro z hz
  obtain ⟨hx₁, hx₂⟩ := h₀
  obtain ⟨hy₁, hy₂⟩ := h₁
  obtain ⟨hz₁, hz₂⟩ := hz
  refine ⟨le_trans (le_min hx₁ hy₁) hz₁, le_trans hz₂ (max_le hx₂ hy₂)⟩


-- created on 2026-10-11
-- updated on 2026-10-17
