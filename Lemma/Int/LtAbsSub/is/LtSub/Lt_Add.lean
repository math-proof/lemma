import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α]
  [LinearOrder α]
  [IsOrderedAddMonoid α]
-- given
  (x a d : α) :
-- imply
  |x - a| < d ↔ a - d < x ∧ x < a + d := by
-- proof
  rw [abs_sub_lt_iff]
  grind


-- created on 2025-12-08
