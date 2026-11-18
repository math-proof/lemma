import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.swap i i = s := by
-- proof
  unfold List.swap
  aesop


-- created on 2025-05-17
-- updated on 2026-11-18
