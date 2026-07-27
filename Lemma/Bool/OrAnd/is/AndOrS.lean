import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.OrAnd.is.AndOrS |
| comm | Bool.AndOrS.is.OrAnd |
| mp | Bool.AndOrS.of.OrAnd |
| mpr | Bool.OrAnd.of.AndOrS |
-/
@[main, comm, mp, mpr]
private lemma main:
-- imply
  p ∧ q ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
-- proof
  aesop


-- created on 2024-07-01
