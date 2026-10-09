import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.Imp.is.ImpNotS |
| comm | Bool.ImpNotS.is.Imp |
| mp | Bool.ImpNotS.of.Imp |
| mpr | Bool.Imp.of.ImpNotS |
-/
@[path, comm, mp, mpr]
private lemma main:
-- imply
  q → p ↔ ¬p → ¬q := by
-- proof
  grind


-- created on 2018-10-09
