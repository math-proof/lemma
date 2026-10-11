import sympy.Basic


@[path]
private lemma main
  {p q r : Prop}
-- given
  (h : (¬p ∨ ¬q) ∨ r) :
-- imply
  p ∧ q → r := by
-- proof
  grind


-- created on 2018-07-22
