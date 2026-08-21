import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Imp.is.ImpAnd.ImpAnd_Not |
| comm | Bool.ImpAnd.ImpAnd_Not.is.Imp |
| mp | Bool.ImpAnd.ImpAnd_Not.of.Imp |
| mpr | Bool.Imp.of.ImpAnd.ImpAnd_Not |
-/
@[main, comm, mp, mpr]
private lemma main
  {p q r : Prop} :
-- imply
  p → q ↔ (p ∧ r → q) ∧ (p ∧ ¬r → q) := by
-- proof
  grind


-- created on 2023-10-03
-- updated on 2026-08-21
