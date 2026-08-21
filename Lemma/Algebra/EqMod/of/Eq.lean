import sympy.Basic


@[main]
private lemma main
  {x y d : ℤ}
-- given
  (h : x = y) :
-- imply
  x % d = y % d :=
-- proof
  congrArg (· % d) h


-- created on 2018-11-22
-- updated on 2026-08-20
