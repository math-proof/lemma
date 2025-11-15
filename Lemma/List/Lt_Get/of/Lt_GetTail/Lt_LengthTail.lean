import sympy.Basic


@[main]
private lemma main
  [LT α]
  {s : List α}
-- given
  (h_i : i < s.tail.length)
  (h : k < s.tail[i]) :
-- imply
  k < s[i + 1]'(by grind) := by
-- proof
  grind


-- created on 2025-11-15
