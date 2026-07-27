import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.AndOr.is.OrAndS |
| comm | Bool.OrAndS.is.AndOr |
| mp | Bool.OrAndS.of.AndOr |
| mpr | Bool.AndOr.of.OrAndS |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  (q ∨ r) ∧ p ↔ q ∧ p ∨ r ∧ p := by
-- proof
  grind


@[main, comm, mp, mpr]
private lemma apart :
-- imply
  (q ∨ r) ∧ p ↔ p ∧ q ∨ r ∧ p := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-07-27
