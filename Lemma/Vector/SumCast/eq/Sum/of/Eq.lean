import Theorem.Data.Vector.Basic.Part2


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
