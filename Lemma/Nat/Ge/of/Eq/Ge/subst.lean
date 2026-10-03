import sympy.Basic


@[main]
private lemma main
  {x y t b k : ℝ}
-- given
  (hk : 0 < k)
  (h_eq : y = x * k + b)
  (h_ge : x ≥ t) :
-- imply
  y ≥ t * k + b := by
-- proof
  have hxk : t * k ≤ x * k := mul_le_mul_of_nonneg_right h_ge hk.le
  rw [h_eq]
  linarith


-- created on 2021-03-19
