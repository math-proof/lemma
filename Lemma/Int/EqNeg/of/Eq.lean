import sympy.Basic


@[main]
private lemma main
  [Neg α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  -a = -b := by
-- proof
  rw [h]


-- created on 2026-09-27
