import sympy.Basic


@[path]
private lemma main
  [Neg α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  -a = -b := by
-- proof
  rw [h]


-- created on 2023-05-03
