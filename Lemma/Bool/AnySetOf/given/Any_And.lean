import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {q : β → Prop}
  {r : α → β → Prop}
-- given
  (h : ∃ x | p x, ∃ y | q y, r x y) :
-- imply
  ∃ x y, r x y ∧ p x ∧ q y := by
-- proof
  obtain ⟨x, hpx, y, hqy, hrxy⟩ := h
  exact ⟨x, y, hrxy, hpx, hqy⟩


-- created on 2026-10-03
