import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Iff.is.IffNotS |
| comm | Bool.IffNotS.is.Iff |
| mp | Bool.IffNotS.of.Iff |
| mpr | Bool.Iff.of.IffNotS |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  (p ↔ q) ↔ (¬p ↔ ¬q) := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2025-08-13
