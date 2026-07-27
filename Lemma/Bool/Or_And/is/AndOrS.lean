import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Or_And.is.AndOrS |
| comm | Bool.AndOrS.is.Or_And |
| mp | Bool.AndOrS.of.Or_And |
| mpr | Bool.Or_And.of.AndOrS |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  r ∨ p ∧ q ↔ (r ∨ p) ∧ (r ∨ q) := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma Comm :
-- imply
  r ∨ p ∧ q ↔ (p ∨ r) ∧ (q ∨ r) := by
-- proof
  aesop


-- created on 2024-07-01
