import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≠ y) :
-- imply
  x > y ∨ x < y :=
-- proof
  (lt_or_gt_of_ne h).symm


-- created on 2023-04-19
