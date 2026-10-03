import sympy.Basic


@[main]
private lemma main
  {a b c d : Prop}
-- given
  (h : a ∨ (b ∨ d) ∧ c) :
-- imply
  a ∨ (b ∧ c) ∨ (d ∧ c) := by
-- proof
  grind


-- created on 2026-10-03
