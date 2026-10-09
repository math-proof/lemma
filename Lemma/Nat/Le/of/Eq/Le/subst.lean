import sympy.Basic


@[path]
private lemma main
  {x y t k b : ℝ}
-- given
  (he : y = x * k + b)
  (hle : x ≤ t)
  (hk : 0 < k) :
-- imply
  y ≤ t * k + b := by
-- proof
  calc _ = x * k + b := he
    _ ≤ t * k + b := by linarith [mul_le_mul_of_nonneg_right hle hk.le]


-- created on 2020-08-08
