import sympy.Basic


@[main]
private lemma collect.given
  {p q r c : Prop}
-- given
  (h : c ∨ (p ∧ q ∧ r)) :
-- imply
  (p ∨ c) ∧ (q ∨ c) ∧ (r ∨ c) := by
-- proof
  rcases h with hc | ⟨hp, hq, hr⟩
  ·
    exact ⟨Or.inr hc, Or.inr hc, Or.inr hc⟩
  ·
    exact ⟨Or.inl hp, Or.inl hq, Or.inl hr⟩


-- created on 2026-09-27
