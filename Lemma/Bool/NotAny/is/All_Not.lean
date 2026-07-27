import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.NotAny.is.All_Not |
| comm | Bool.All_Not.is.NotAny |
| mp | Bool.All_Not.of.NotAny |
| mpr | Bool.NotAny.of.All_Not |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (p : α → Prop) :
-- imply
  (¬∃ x : α, p x) ↔ ∀ x : α, ¬p x := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-07-27
