import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Zero α]
  {s s' : List ℕ}
-- given
  (h : s = s') :
-- imply
  cast (congrArg (Tensor α) h) 0 = 0 := by
-- proof
  aesop


-- created on 2025-11-30
-- updated on 2026-11-20
