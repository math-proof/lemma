import sympy.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a :=
-- proof
  h.symm


-- created on 2018-05-25
