import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.Any.is.NotAll_Not |
| comm | Bool.NotAll_Not.is.Any |
| mp | Bool.NotAll_Not.of.Any |
| mpr | Bool.Any.of.NotAll_Not |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-07-27
