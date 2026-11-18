import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path]
private lemma main
-- given
  (head : List α)
  (tail : List (List α)) :
-- imply
  (itertools.product (head :: tail)).length = head.length * (itertools.product tail).length := by
-- proof
  unfold itertools.product
  simp_all


-- created on 2025-06-13
-- updated on 2026-11-18
