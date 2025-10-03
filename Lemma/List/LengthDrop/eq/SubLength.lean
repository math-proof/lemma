import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.drop i).length = s.length - i := by
-- proof
  simp


-- created on 2025-06-07
-- updated on 2025-06-17
