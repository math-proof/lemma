import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  |x| = x :=
-- proof
  abs_of_pos h


-- created on 2025-10-01
-- updated on 2026-07-06
