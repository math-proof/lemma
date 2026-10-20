import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c x : ℝ}
-- given
  (h₀ : x ∈ Set.Icc a b)
  (h₁ : x ≤ c)
  (h₂ : c ≤ b) :
-- imply
  x ∈ Set.Icc a c ∧ c ≤ b := by
-- proof
  rw [Set.mem_Icc] at h₀
  exact ⟨⟨h₀.1, h₁⟩, h₂⟩


-- created on 2023-08-20
-- updated on 2026-10-17
