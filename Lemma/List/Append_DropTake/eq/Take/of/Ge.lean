import Initialize.Tactic.Attr.Basic
import Theorem.List.TakeTake.eq.Take.of.Ge
open List


@[path]
private lemma main
-- given
  (h : m ≥ n)
  (s : List α) :
-- imply
  s.take n ++ (s.take m).drop n = s.take m := by
-- proof
  rw [← TakeTake.eq.Take.of.Ge h]
  simp


-- created on 2025-10-28
-- updated on 2026-11-22
