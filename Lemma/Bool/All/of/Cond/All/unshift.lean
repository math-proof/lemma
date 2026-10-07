import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
  {p : ℤ → Prop}
-- given
  (h₁ : p (a - 1))
  (h₂ : ∀ k ∈ Set.Ico a b, p k) :
-- imply
  ∀ k ∈ Set.Ico (a - 1) b, p k := by
-- proof
  intro k hk
  obtain ⟨hka, hku⟩ := hk
  by_cases h : a ≤ k
  · exact h₂ k ⟨h, hku⟩
  · have hka' : k = a - 1 := by omega
    rw [hka']
    exact h₁


-- created on 2019-03-13
