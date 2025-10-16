import sympy.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≥ y)
  (k : ℕ) :
-- imply
  k * x ≥ k * y := by
-- proof
  induction k <;>
    simp_all


-- created on 2025-03-31
