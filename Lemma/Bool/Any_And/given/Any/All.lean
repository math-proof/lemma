import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
  {A : Set α}
-- given
  (h : ∃ x ∈ A, p x ∧ q x) :
-- imply
  (∃ x ∈ A, p x) ∧ (∃ x ∈ A, q x) := by
-- proof
  constructor
  ·
    obtain ⟨x, hx, hp, _⟩ := h
    exact ⟨x, hx, hp⟩
  ·
    obtain ⟨x, hx, _, hq⟩ := h
    exact ⟨x, hx, hq⟩


-- created on 2018-12-03
