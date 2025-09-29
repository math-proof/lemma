import sympy.Basic


@[main]
private lemma left
  {a b : ℕ}
-- given
  (h : b + a ≤ b) :
-- imply
  a = 0 := by
-- proof
  simp_all


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a + b ≤ b) :
-- imply
  a = 0 := by
-- proof
  simp_all


-- created on 2025-05-24
