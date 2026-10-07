import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  {p : ℤ → Prop}
-- given
  (h₁ : p b)
  (h₂ : ∀ k ∈ Set.Ico a b, p k) :
-- imply
  ∀ k ∈ Set.Ico a (b + 1), p k := by
-- proof
  intro k hk
  by_cases h : k < b
  · exact h₂ k ⟨hk.1, h⟩
  · obtain ⟨hka, hku⟩ := hk
    have hkb : k = b := by omega
    rw [hkb]
    exact h₁


-- created on 2019-03-12
