import sympy.Basic


@[path, fin]
private lemma main
  {s : List α}
-- given
  (h : i < s.tail.length) :
-- imply
  s.tail[i] = s[i + 1]'(by grind) := by
-- proof
  grind


-- created on 2025-10-10
