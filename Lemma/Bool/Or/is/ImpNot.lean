import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Or.is.ImpNot |
| comm | Bool.ImpNot.is.Or |
| mp | Bool.ImpNot.of.Or |
| mpr | Bool.Or.of.ImpNot |
-/
@[main, comm, mp, mpr]
private lemma main :
-- imply
  p ∨ q ↔ ¬p → q := by
-- proof
  grind


-- created on 2025-01-12
-- updated on 2026-07-27
