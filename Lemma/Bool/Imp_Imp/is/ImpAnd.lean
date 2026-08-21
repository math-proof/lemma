import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp_Imp.is.ImpAnd |
| comm | Bool.ImpAnd.is.Imp_Imp |
| mp | Bool.ImpAnd.of.Imp_Imp |
| mpr | Bool.Imp_Imp.of.ImpAnd |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  tauto


-- created on 2024-07-01
-- updated on 2026-08-21
