import sympy.Basic


@[main]
private lemma reverse
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a :=
-- proof
  h.symm


-- created on 2019-04-19
