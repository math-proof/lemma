import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : p ∧ q → r) :
-- imply
  q → p → r := by
-- proof
  intro hq hp
  exact h ⟨hp, hq⟩


-- created on 2026-10-03
