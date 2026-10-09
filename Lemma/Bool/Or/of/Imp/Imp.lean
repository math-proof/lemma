import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h₀ : a > b → q₀)
  (h₁ : a ≤ b → q₁) :
-- imply
  a > b ∧ q₀ ∨ a ≤ b ∧ q₁ := by
-- proof
  by_cases h : a > b
  ·
    exact Or.inl ⟨h, h₀ h⟩
  ·
    have h' := not_lt.mp h
    exact Or.inr ⟨h', h₁ h'⟩


-- created on 2022-04-01
