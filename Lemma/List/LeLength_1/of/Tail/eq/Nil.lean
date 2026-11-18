import Initialize.Tactic.Attr.Basic
import Def.Data.List.Slice


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.tail = []) :
-- imply
  s.length ≤ 1 := by
-- proof
  cases s <;> simp_all


-- created on 2025-05-05
-- updated on 2026-11-18
