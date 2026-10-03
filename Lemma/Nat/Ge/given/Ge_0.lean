import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  x - y ≥ 0 := by
-- proof
  exact sub_nonneg.mpr h


-- created on 2026-10-03
