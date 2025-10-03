import sympy.Basic


@[main]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  (s.take 1).prod = s.headD 1 := by
-- proof
  cases s <;>
    simp


-- created on 2025-07-15
