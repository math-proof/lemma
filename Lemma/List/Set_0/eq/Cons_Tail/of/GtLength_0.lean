import Theorem.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Initialize.Tactic.Attr.Basic
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (a : α) :
-- imply
  s.set 0 a = a :: s.tail := by
-- proof
  rw [Set.eq.AppendTake__Cons_Drop.of.GtLength h]
  simp


-- created on 2025-07-12
-- updated on 2026-11-20
