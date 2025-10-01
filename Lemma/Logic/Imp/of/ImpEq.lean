import sympy.Basic


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h : a = b → p b) :
-- imply
  a = b → p a := by
-- proof
  aesop


-- created on 2025-10-01
