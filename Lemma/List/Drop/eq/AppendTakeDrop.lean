import sympy.Basic


@[main, comm]
private lemma main
-- given
  (s : List α)
  (i d : ℕ):
-- imply
  s.drop i = (s.drop i).take d ++ s.drop (i + d) := by
-- proof
  simp


-- created on 2025-10-15
