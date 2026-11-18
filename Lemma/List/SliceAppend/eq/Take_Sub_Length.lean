import Initialize.Tactic.Attr.Basic
import Def.Data.List.List.Basic


@[path]
private lemma main
-- given
  (a b : List α)
  (n : ℕ) :
-- imply
  (a ++ b).slice a.length n = b.take (n - a.length) := by
-- proof
  unfold List.slice List.array_slice
  aesop


-- created on 2025-05-18
-- updated on 2026-11-18
