import sympy.Basic


@[main]
private lemma main
  [HPow α β α]
  {a b : β}
-- given
  (h : a = b)
  (x : α) :
-- imply
  x ^ a = x ^ b := by
-- proof
  rw [h]


-- created on 2018-03-12
