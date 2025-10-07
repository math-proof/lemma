import sympy.Basic


@[main]
private lemma main
  {p : Prop}
-- given
  (h : p) :
-- imply
  p ↔ True := by
-- proof
  simp [h]


-- created on 2025-03-27
