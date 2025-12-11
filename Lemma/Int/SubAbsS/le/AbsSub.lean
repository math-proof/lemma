import sympy.Basic


@[main]
private lemma main
  [AddCommGroup G]
  [LinearOrder G]
  [IsOrderedAddMonoid G]
-- given
  (a b : G) :
-- imply
  |a| - |b| ≤ |a - b| :=
-- proof
  abs_sub_abs_le_abs_sub a b


-- created on 2025-12-11
