import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path]
private lemma main:
-- imply
  itertools.product ([] : List (List α)) = [[]] := by
-- proof
  unfold itertools.product
  simp


-- created on 2025-06-14
-- updated on 2026-11-18
