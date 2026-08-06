import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp_Ite.is.Imp |
| comm | Bool.Imp.is.Imp_Ite |
| mp | Bool.Imp.of.Imp_Ite |
| mpr | Bool.Imp_Ite.of.Imp |
-/
@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  {α : Type*}
  {a b c : α} :
-- imply
  (p → (if p then a else b) = c) ↔ (p → a = c) := by
-- proof
  grind


-- created on 2019-10-05
-- updated on 2026-08-06
