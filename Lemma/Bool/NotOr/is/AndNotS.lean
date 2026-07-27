import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.NotOr.is.AndNotS |
| comm | Bool.AndNotS.is.NotOr |
| mp | Bool.AndNotS.of.NotOr |
| mpr | Bool.NotOr.of.AndNotS |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
-- proof
  not_or


-- created on 2024-07-01
-- updated on 2025-10-25
