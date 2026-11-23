import Initialize.Tactic.Attr.Basic
import Theorem.List.DropTake.eq.ListGet.of.GtLength
open List


@[path]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.take (i + 1)).drop i = [s[i]] := by
-- proof
  apply DropTake.eq.ListGet.of.GtLength


-- created on 2025-10-27
-- updated on 2026-11-22
