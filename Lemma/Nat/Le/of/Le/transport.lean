import sympy.Basic


@[path]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a y : α}
-- given
  (h : x + a ≤ y) :
-- imply
  x ≤ y - a := by
-- proof
  exact le_sub_iff_add_le.mpr h


-- created on 2022-04-01
