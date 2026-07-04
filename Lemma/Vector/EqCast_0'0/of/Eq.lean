import sympy.vector.vector


@[main]
private lemma main
  [Zero α]
  -- given
  (h : n = n') :
-- imply
  cast (congrArg (List.Vector α) h) 0 = 0 := by
-- proof
  aesop


-- created on 2025-11-30
