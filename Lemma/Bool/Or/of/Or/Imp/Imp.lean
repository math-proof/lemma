import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : p₀ ∨ p₁)
  (h₁ : p₀ → q₀)
  (h₂ : p₁ → q₁) :
-- imply
  p₀ ∧ q₀ ∨ p₁ ∧ q₁ :=
-- proof
  h₀.imp (fun h => ⟨h, h₁ h⟩) (fun h => ⟨h, h₂ h⟩)


-- created on 2026-09-27
