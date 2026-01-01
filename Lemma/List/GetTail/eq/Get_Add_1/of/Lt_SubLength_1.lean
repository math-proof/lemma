import sympy.Basic


@[main, fin]
private lemma main
  {s : List α}
-- given
  (h : i < s.length - 1) :
-- imply
  s.tail[i]'(by simpa) = s[i + 1] := by
-- proof
  grind


-- created on 2025-10-05
