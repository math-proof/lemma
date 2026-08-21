import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {r : Prop}
-- given
  (h_r : r)
  (h : ∃ x : α, p x) :
-- imply
  ∃ x : α, p x ∧ r := by
-- proof
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, h_r⟩


-- created on 2018-08-24
-- updated on 2026-08-20
