import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {e a b c : ℝ}
-- given
  (h₀ : e ∈ Set.Icc a b)
  (h₁ : c ∈ Set.Icc a b) :
-- imply
  e ∈ Set.Ico a c ∨ e ∈ Set.Icc c b := by
-- proof
  obtain ⟨h_ge, h_le⟩ := h₀
  obtain ⟨_, _⟩ := h₁
  if hce : e < c then
    exact Or.inl ⟨h_ge, hce⟩
  else
    exact Or.inr ⟨not_lt.mp hce, h_le⟩


-- created on 2026-10-11
-- updated on 2026-10-17
