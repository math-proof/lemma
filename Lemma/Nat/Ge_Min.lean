import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y : α} :
-- imply
  x ≥ min x y :=
-- proof
  min_le_left x y


-- created on 2023-04-23
