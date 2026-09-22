import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α]
  [LinearOrder α]
  [IsOrderedAddMonoid α]
-- given
  {x y : α}
  (h : x > y) :
-- imply
  |x - y| = x - y := by
  have hpos : 0 < x - y := sub_pos.mpr h
  exact abs_of_pos hpos


-- created on 2019-07-21
