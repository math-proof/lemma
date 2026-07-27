import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp.is.OrNot |
| comm | Bool.OrNot.is.Imp |
| mp | Bool.OrNot.of.Imp |
| mpr | Bool.Imp.of.OrNot |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  p → q ↔ ¬p ∨ q := by
-- proof
  grind


-- created on 2024-07-01
