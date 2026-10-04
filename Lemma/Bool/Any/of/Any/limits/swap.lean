import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p : α → β → Prop}
  {r : α → Prop}
  {s : β → Prop}
-- given
  (h : ∃ x | r x, ∃ y | s y, p x y) :
-- imply
  ∃ y | s y, ∃ x | r x, p x y := by
-- proof
  obtain ⟨x, hr, y, hs, hp⟩ := h
  exact ⟨y, hs, x, hr, hp⟩


-- created on 2019-02-15
