import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp.is.Or_Not |
| comm | Bool.Or_Not.is.Imp |
| mp | Bool.Or_Not.of.Imp |
| mpr | Bool.Imp.of.Or_Not |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  (p → q ↔ q ∨ ¬p) := by
-- proof
  grind


-- created on 2025-04-05
-- updated on 2026-07-27
