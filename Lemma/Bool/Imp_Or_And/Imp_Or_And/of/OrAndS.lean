import sympy.Basic


@[main]
private lemma main
  {p q r s : Prop}
-- given
  (h : p ∧ q ∨ r ∧ s) :
-- imply
  (p → q ∨ r ∧ s) ∧ (r → s ∨ p ∧ q) := by
-- proof
  constructor
  ·
    intro hp
    rcases h with ⟨_, hq⟩ | h
    ·
      exact Or.inl hq
    ·
      exact Or.inr h
  ·
    intro hr
    rcases h with h | ⟨_, hs⟩
    ·
      exact Or.inr h
    ·
      exact Or.inl hs


-- created on 2018-11-24
-- updated on 2026-08-20
