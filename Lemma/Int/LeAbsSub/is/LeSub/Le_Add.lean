import sympy.Basic


@[main]
private lemma main
  [AddCommGroup G]
  [LinearOrder G]
  [IsOrderedAddMonoid G]
  -- given
  (x a d : G) :
-- imply
  |x - a| ≤ d ↔ a - d ≤ x ∧ x ≤ a + d := by
-- proof
  rw [abs_sub_le_iff]
  grind


-- created on 2025-12-10
