import sympy.Basic


@[main]
private lemma main
  {p q c₁ c₂ : Prop}
-- given
  (h₁ : c₁)
  (h₂ : c₂)
  (h : p ∨ q) :
-- imply
  (p ∧ c₁ ∧ c₂) ∨ (q ∧ c₁ ∧ c₂) := by
-- proof
  obtain hp | hq := h
  ·
    exact Or.inl ⟨hp, h₁, h₂⟩
  ·
    exact Or.inr ⟨hq, h₁, h₂⟩


-- created on 2019-03-15
