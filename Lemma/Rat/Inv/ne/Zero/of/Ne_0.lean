import sympy.Basic


@[main]
private lemma main
  [DivisionRing α]
  {x : α}
-- given
  (h : x ≠ 0) :
-- imply
  1 / x ≠ 0 :=
-- proof
  one_div_ne_zero h


-- created on 2026-09-27
