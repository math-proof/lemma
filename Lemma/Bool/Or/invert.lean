import sympy.Basic


@[path]
private lemma main
  {p q : Prop} :
-- imply
  p ∨ q ↔ (p ∧ ¬q) ∨ q := by
-- proof
  constructor
  · intro h
    obtain hp | hq := h
    · if hq : q then
        exact Or.inr hq
      else
        exact Or.inl ⟨hp, hq⟩
    · exact Or.inr hq
  · intro h
    obtain h | hq := h
    · exact Or.inl h.1
    · exact Or.inr hq


-- created on 2021-12-17
