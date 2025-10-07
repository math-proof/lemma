import sympy.Basic


@[main]
private lemma left
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ q x) :
-- imply
  ∃ x : α, p x := by
-- proof
  let ⟨x, hLeft, hRight⟩ := h
  exact ⟨x, hLeft⟩


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∧ q x) :
-- imply
  ∃ x : α, q x := by
-- proof
  let ⟨x, hLeft, hRight⟩ := h
  exact ⟨x, hRight⟩


-- created on 2024-07-01
