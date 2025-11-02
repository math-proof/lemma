import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.tail.drop i = s.drop (i + 1) := by
-- proof
  simp


-- created on 2025-11-02
