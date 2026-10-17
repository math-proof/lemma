import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x₀ x₁ w : ℝ}
-- given
  (h₀ : x₀ ∈ Set.Icc a b)
  (h₁ : x₁ ∈ Set.Icc a b)
  (h₂ : w ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  x₀ * w + x₁ * (1 - w) ∈ Set.Icc a b := by
-- proof
  rw [Set.mem_Icc] at h₀ h₁ h₂ ⊢
  constructor
  · nlinarith
  · nlinarith


-- created on 2026-10-11
-- updated on 2026-10-17
