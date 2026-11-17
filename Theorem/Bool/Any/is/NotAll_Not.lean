module

public import Initialize.Tactic.Attr.Basic

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.Any.is.NotAll_Not |
| comm | Bool.NotAll_Not.is.Any |
| mp | Bool.NotAll_Not.of.Any |
| mpr | Bool.Any.of.NotAll_Not |
-/
@[comm, mp, mpr]
public theorem Bool.Any.is.NotAll_Not
-- given
  (p : α → Prop) :
-- imply
  (∃ x : α, p x) ↔ ¬∀ x : α, ¬p x := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-10-26
