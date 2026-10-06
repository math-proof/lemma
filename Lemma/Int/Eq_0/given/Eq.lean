import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a - b = 0) :
-- imply
  a = b :=
-- proof
  sub_eq_zero.mp h


-- created on 2021-06-26
