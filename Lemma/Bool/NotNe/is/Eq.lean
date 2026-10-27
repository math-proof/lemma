import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.NotNe.is.Eq |
| comm | Bool.Eq.is.NotNe |
| mp | Bool.Eq.of.NotNe |
| mpr | Bool.NotNe.of.Eq |
-/
@[path, comm, mp, mpr]
private lemma main
-- given
  (a b : α) :
-- imply
  ¬a ≠ b ↔ a = b := by
-- proof
  aesop


-- created on 2025-03-30
-- updated on 2026-10-26
