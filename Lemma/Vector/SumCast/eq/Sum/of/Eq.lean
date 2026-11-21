import Def.Data.Vector.Basic
import Theorem.Data.Vector.Basic


@[path]
private lemma main
  [Add α] [Zero α]
-- given
  (h : n = n')
  (v : List.Vector α n) :
-- imply
  (cast (congrArg (List.Vector α) h) v).sum = v.sum := by
-- proof
  subst h
  rfl


-- created on 2025-11-01
-- updated on 2026-11-20
