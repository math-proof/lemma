import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [LinearOrder α]
  {a b : α} :
-- imply
  a < b ↔ a ≤ b ∧ a ≠ b := by
-- proof
  grind


-- created on 2025-11-13
-- updated on 2026-07-04
