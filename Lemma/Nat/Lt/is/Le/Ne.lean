import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Lt.is.Le.Ne |
| comm | Nat.Le.Ne.is.Lt |
| mp | Nat.Le.Ne.of.Lt |
| mpr | Nat.Lt.of.Le.Ne |
-/
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
