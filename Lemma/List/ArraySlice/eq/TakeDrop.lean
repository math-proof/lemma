import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path, comm]
private lemma main
-- given
  (s : List α) :
-- imply
  s.array_slice i d = (s.drop i).take d := by
-- proof
  simp [List.array_slice]


-- created on 2025-05-08
-- updated on 2026-11-18
