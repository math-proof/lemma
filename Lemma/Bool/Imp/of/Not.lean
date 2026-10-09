import sympy.Basic


@[path]
private lemma main
  {p q : Prop}
-- given
  (h : ¬p) :
-- imply
  p → q := by
-- proof
  intro hp
  contradiction


-- created on 2024-07-01
