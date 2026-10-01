import sympy.Basic


@[main]
private lemma given
  {p q c₁ c₂ : Prop}
-- given
  (h : (p ∧ c₁ ∧ c₂) ∨ (q ∧ c₁ ∧ c₂)) :
-- imply
  c₁ ∧ c₂ ∧ (p ∨ q) := by
-- proof
  rcases h with ⟨hp, h₁, h₂⟩ | ⟨hq, h₁, h₂⟩
  ·
    exact ⟨h₁, h₂, Or.inl hp⟩
  ·
    exact ⟨h₁, h₂, Or.inr hq⟩


-- created on 2019-03-15
