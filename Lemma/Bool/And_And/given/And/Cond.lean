import sympy.Basic


@[main]
private lemma main
  {p q r : Prop}
-- given
  (h : (p ∧ q) ∧ r) :
-- imply
  p ∧ q ∧ r := by
-- proof
  aesop


-- created on 2026-10-03
