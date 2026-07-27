import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any_And.is.AndAny |
| comm | Bool.AndAny.is.Any_And |
| mp | Bool.AndAny.of.Any_And |
| mpr | Bool.Any_And.of.AndAny |
-/
@[main, comm, mp, mpr]
private lemma main
  {r : Prop}
  {p : α → Prop} :
-- imply
  (∃ x : α, p x ∧ r) ↔ (∃ x : α, p x) ∧ r := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-07-27
