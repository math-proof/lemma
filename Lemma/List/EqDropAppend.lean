import Def.Data.List.List.Basic
@[path]
private lemma main
-- given
  (a b : List α) :
-- imply
  (a ++ b).drop a.length = b := by
-- proof
  aesop


-- created on 2025-05-08
-- updated on 2026-10-26
