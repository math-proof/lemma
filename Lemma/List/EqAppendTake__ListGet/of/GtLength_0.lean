import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.take (s.length - 1) ++ [s[s.length - 1]] = s := by
-- proof
  simp
  omega


-- created on 2025-10-28
