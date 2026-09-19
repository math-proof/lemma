import sympy.Basic


@[main]
private lemma main
  {a b r : ℝ}
-- given
  (hr : 0 ≤ r)
  (ha : 0 < a)
  (hb : 0 < b)
  (h : a ≤ b) :
-- imply
  b ^ (-r) ≤ a ^ (-r) := calc
-- proof
  _ = (b ^ r)⁻¹ := Real.rpow_neg hb.le r
  _ ≤ (a ^ r)⁻¹ := by
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos hb r) (Real.rpow_pos_of_pos ha r)).mpr
    exact Real.rpow_le_rpow ha.le h hr
  _ = _ := (Real.rpow_neg ha.le r).symm


-- created on 2026-09-18
