import sympy.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (i d : ℕ):
-- imply
  v.drop i = (v.drop i).take d ++ v.drop (i + d) := by
-- proof
  simp


-- created on 2025-10-15
