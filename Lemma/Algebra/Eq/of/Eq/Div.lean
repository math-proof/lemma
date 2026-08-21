import sympy.Basic


@[main]
private lemma main
  [Div α]
  {x y d : α}
-- given
  (h : x = y) :
-- imply
  x / d = y / d :=
-- proof
  congrArg (· / d) h


-- created on 2018-08-21
-- updated on 2026-08-20
