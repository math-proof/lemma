import sympy.Basic


@[path]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x, q x ∧ p x) :
-- imply
  ∃ x, p x ∧ q x := by
-- proof
  obtain ⟨x, hq, hp⟩ := h
  exact ⟨x, hp, hq⟩


-- created on 2020-09-05
