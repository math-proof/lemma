import sympy.Basic


@[path]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a y : α} :
-- imply
  x + a > y ↔ a > y - x := by
-- proof
  constructor
  · intro h
    rw [add_comm x a] at h
    exact sub_lt_iff_lt_add.mpr h
  · intro h
    rw [add_comm x a]
    exact sub_lt_iff_lt_add.mp h


-- created on 2026-10-03
