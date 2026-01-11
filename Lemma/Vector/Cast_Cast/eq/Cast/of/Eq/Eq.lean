import sympy.Basic


@[main]
private lemma main
-- given
  (h_n : n = n')
  (h_n' : n' = n'')
  (x : List.Vector α n) :
-- imply
  cast (congrArg (List.Vector α) h_n') (cast (congrArg (List.Vector α) h_n) x) = cast (by aesop) x := by
-- proof
  simp


-- created on 2026-01-10
