import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α} :
-- imply
  x ≥ min x y :=
-- proof
  min_le_left x y


-- created on 2026-09-27
