import sympy.Basic


@[main, fin]
private lemma main
  {s : List α}
-- given
  (h_j : s.length > j)
  (h_i : i < j)
  (a : α) :
-- imply
  (s.insertIdx i a)[j]'(by grind) = s[j - 1] := by
-- proof
  grind


-- created on 2025-11-17
