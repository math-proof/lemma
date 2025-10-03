import sympy.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  v.take n ++ v.drop n = v := by
-- proof
  simp


-- created on 2025-05-09
