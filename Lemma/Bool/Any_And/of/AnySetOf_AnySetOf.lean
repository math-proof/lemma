import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {q : β → Prop}
  {r : α → β → Prop}
-- given
  (h : ∃ y | q y, ∃ x | p x, r x y) :
-- imply
  ∃ x y, p x ∧ q y ∧ r x y := by
-- proof
  let ⟨y, qy, x, px, rxy⟩ := h
  use x, y


-- created on 2025-04-27
