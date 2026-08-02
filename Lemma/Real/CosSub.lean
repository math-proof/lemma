import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x - y) = Real.cos (y - x) := by
-- proof
  rw [← Real.cos_neg, neg_sub]


-- created on 2025-08-02
