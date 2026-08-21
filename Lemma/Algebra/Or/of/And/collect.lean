import sympy.Basic


@[main]
private lemma collect
  {p q r : Prop}
-- given
  (h : p ∧ r ∨ q ∧ r) :
-- imply
  r ∧ (p ∨ q) := by
-- proof
  rcases h with ⟨hp, hr⟩ | ⟨hq, hr⟩
  ·
    exact ⟨hr, Or.inl hp⟩
  ·
    exact ⟨hr, Or.inr hq⟩


-- created on 2020-02-18
-- updated on 2026-08-20
