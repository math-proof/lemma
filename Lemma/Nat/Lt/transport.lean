import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a y : α}
-- given
  (h : x + a < y) :
-- imply
  x < y - a := by
-- proof
  exact lt_sub_iff_add_lt.mpr h


-- created on 2026-10-03
