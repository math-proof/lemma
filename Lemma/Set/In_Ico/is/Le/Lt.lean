import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.In_Ico.is.Le.Lt |
| comm | Set.Le.Lt.is.In_Ico |
| mp | Set.Le.Lt.of.In_Ico |
| mpr | Set.In_Ico.of.Le.Lt |
-/
@[path, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (a b : α) :
-- imply
  x ∈ Ico a b ↔ a ≤ x ∧ x < b := by
-- proof
  rfl


-- created on 2023-04-16
-- updated on 2026-10-26
