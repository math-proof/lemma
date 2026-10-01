import sympy.Basic


@[main]
private lemma main
  {f : α → Prop}
  {g : β → Prop}
  {r : α → β → Prop}
-- given
  (h : ∃ x ∈ {x | f x}, ∃ y ∈ {y | g y}, r x y) :
-- imply
  ∃ x ∈ {x | f x}, ∃ y ∈ {y | g y}, r x y ∧ f x ∧ g y := by
-- proof
  obtain ⟨x, hx, y, hy, hr⟩ := h
  exact ⟨x, hx, y, hy, hr, hx, hy⟩


-- created on 2026-09-27
