import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any_And.is.Cond.Any |
| comm | Bool.Cond.Any.is.Any_And |
| mp | Bool.Cond.Any.of.Any_And |
| mpr | Bool.Any_And.of.Cond.Any |
-/
@[main, comm, mp, mpr]
private lemma main
  {p : α → Prop}
  {r : Prop} :
-- imply
  (∃ x : α, p x ∧ r) ↔ r ∧ ∃ x : α, p x := by
-- proof
  grind


-- created on 2018-08-24
-- updated on 2026-08-23
