import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.NotImp.is.And_Not |
| comm | Bool.And_Not.is.NotImp |
| mp | Bool.And_Not.of.NotImp |
| mpr | Bool.NotImp.of.And_Not |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  ¬(p → q) ↔ p ∧ ¬q := by
-- proof
  aesop


-- created on 2024-07-01
-- updated on 2025-07-30
