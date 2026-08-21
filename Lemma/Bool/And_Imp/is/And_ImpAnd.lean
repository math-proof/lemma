import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.And_Imp.is.And_ImpAnd |
| comm | Bool.And_ImpAnd.is.And_Imp |
| mp | Bool.And_ImpAnd.of.And_Imp |
| mpr | Bool.And_Imp.of.And_ImpAnd |
-/
@[main, comm, mp, mpr]
private lemma main
  {p q r : Prop} :
-- imply
  p ∧ (q → r) ↔ p ∧ (p ∧ q → r) := by
-- proof
  grind


-- created on 2019-08-15
-- updated on 2026-08-21
