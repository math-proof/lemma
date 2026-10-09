import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.And_Or.is.OrAndS |
| comm | Bool.OrAndS.is.And_Or |
| mp | Bool.OrAndS.of.And_Or |
| mpr | Bool.And_Or.of.OrAndS |
-/
@[path, comm, mp, mpr]
private lemma main :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ p ∧ r := by
-- proof
  grind


@[path, comm, mp, mpr]
private lemma apart :
-- imply
  p ∧ (q ∨ r) ↔ p ∧ q ∨ r ∧ p  := by
-- proof
  rw [And.comm (b := p)]
  apply main


-- created on 2018-01-21
