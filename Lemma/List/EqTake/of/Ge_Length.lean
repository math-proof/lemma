import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : n ≥ a.length):
-- imply
  a.take n = a := by
-- proof
  aesop


-- created on 2025-06-16
