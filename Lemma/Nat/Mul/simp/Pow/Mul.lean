import sympy.Basic


@[main]
private lemma base
  {x y z : ℝ}
  {t : ℤ} :
-- imply
  x ^ t * y ^ t * z * 2 ^ x = (x * y) ^ t * z * 2 ^ x := by
-- proof
  rw [mul_zpow]


-- created on 2026-09-27
