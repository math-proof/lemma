import sympy.Basic


@[main]
private lemma main
  {a b r : ℝ}
-- given
  (hr : 0 < r)
  (ha : 0 ≤ a)
  (hb : 0 ≤ b)
  (h : a ≤ b ^ r) :
-- imply
  a ^ r⁻¹ ≤ b := calc
-- proof
  _ ≤ (b ^ r) ^ r⁻¹ := Real.rpow_le_rpow ha h (inv_nonneg.2 hr.le)
  _ = _ := by
    rw [← Real.rpow_mul hb, mul_inv_cancel₀ hr.ne', Real.rpow_one]


-- created on 2026-09-18
