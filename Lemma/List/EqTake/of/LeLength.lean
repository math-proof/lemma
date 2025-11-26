import sympy.Basic


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ n):
-- imply
  s.take n = s := by
-- proof
  aesop


-- created on 2025-06-16
