import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp.is.ImpNotS |
| comm | Bool.ImpNotS.is.Imp |
| mp | Bool.ImpNotS.of.Imp |
| mpr | Bool.Imp.of.ImpNotS |
-/
@[main, comm, mp, mpr]
private lemma main:
-- imply
  q → p ↔ ¬p → ¬q := by
-- proof
  grind


-- created on 2018-10-09
