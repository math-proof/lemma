import Initialize.Tactic.Attr.Basic
import Theorem.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Theorem.List.TakeCons.eq.List
import Theorem.List.DropTake.eq.TakeDrop
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  rw [DropTake.eq.TakeDrop]
  simp
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength h]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
-- updated on 2026-11-22
