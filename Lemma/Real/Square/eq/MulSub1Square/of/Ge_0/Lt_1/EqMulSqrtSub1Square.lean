import sympy.Basic


/--
Semi-minor axis of an ellipse: \(b=a\sqrt{1-e^2}\) gives \(b^2=a^2(1-e^2)\).
-/
@[main]
private lemma main
  {a b e : ℝ}
-- given
  (he₀ : 0 ≤ e)
  (he₁ : e < 1)
  (hb : b = a * Real.sqrt (1 - e ^ 2)) :
-- imply
  b ^ 2 = a ^ 2 * (1 - e ^ 2) := by
-- proof
  have h : 0 ≤ 1 - e ^ 2 := by nlinarith
  rw [hb, mul_pow, Real.sq_sqrt h]


-- created on 2026-09-29