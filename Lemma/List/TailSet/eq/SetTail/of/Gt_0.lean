import Theorem.Nat.EqAddSub.of.Ge
import Initialize.Tactic.Attr.Basic
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | List.TailSet.eq.SetTail.of.Gt_0 |
| comm | List.SetTail.eq.TailSet.of.Gt_0 |
-/
@[path, comm]
private lemma main
-- given
  (h : i > 0)
  (s : List α)
  (a : α) :
-- imply
  (s.set i a).tail = s.tail.set (i - 1) a := by
-- proof
  simp
  rw [EqAddSub.of.Ge h]


-- created on 2025-07-05
-- updated on 2026-11-20
