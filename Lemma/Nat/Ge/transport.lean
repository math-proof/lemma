import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x a y : α}
-- given
  (h : x + a ≥ y) :
-- imply
  x ≥ y - a := by
-- proof
  rw [add_comm x a] at h
  exact sub_le_iff_le_add'.mpr h


-- created on 2026-10-03
