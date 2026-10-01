import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
  {n : ℤ}
-- given
  (h : Even n) :
-- imply
  (x - y) ^ n = (y - x) ^ n := by
-- proof
  rw [show y - x = -(x - y) by ring, Even.neg_zpow h]


-- created on 2026-09-27
