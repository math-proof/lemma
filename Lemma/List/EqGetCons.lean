import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path, fin]
private lemma main
-- given
  (head : α)
  (tail : List α) :
-- imply
  (head :: tail)[0] = head := by
-- proof
  simp


-- created on 2025-11-07
-- updated on 2026-11-18
