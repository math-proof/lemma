import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.NotAnd.is.OrNotS |
| comm | Bool.OrNotS.is.NotAnd |
| mp | Bool.OrNotS.of.NotAnd |
| mpr | Bool.NotAnd.of.OrNotS |
-/
@[path, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-07-27
