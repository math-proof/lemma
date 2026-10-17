import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x : ℝ, a * x ^ 2 + b * x + c < 0 := by
-- proof
  if ha : 0 < a then
    refine ⟨-b / (2 * a), ?_⟩
    have hne : (2 : ℝ) * a ≠ 0 := by positivity
    have heq : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = -(b ^ 2 - 4 * a * c) / (4 * a) := by
      field_simp [hne]
      ring
    rw [heq]
    apply div_neg_of_neg_of_pos
    ·
      linarith
    ·
      positivity
  else if ha0 : a = 0 then
    have hb : b ≠ 0 := sq_pos_iff.mp (by simpa [ha0] using h₀)
    refine ⟨(-c - 1) / b, ?_⟩
    simp only [ha0, zero_mul, zero_add]
    have heq : b * ((-c - 1) / b) + c = -1 := by
      field_simp [hb]
      ring
    linarith
  else
    have ha' : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha0
    let x : ℝ := (|b| + |c| + 1) * (1 + (-a)⁻¹)
    have hna : 0 < -a := by linarith
    have hx : 0 < x := by positivity
    have hxbig : (|b| + |c| + 1) / (-a) ≤ x := by
      rw [div_le_iff₀ hna]
      have hmul : x * (-a) = (|b| + |c| + 1) * ((-a) + 1) := by
        unfold x
        field_simp [hna.ne']
        ring
      nlinarith [abs_nonneg b, abs_nonneg c, hna]
    refine ⟨x, ?_⟩
    have hax : a * x ≤ -(|b| + |c| + 1) := by
      have hth : a * ((|b| + |c| + 1) / (-a)) = -(|b| + |c| + 1) := by
        field_simp [hna.ne']
      have hmul : a * x ≤ a * ((|b| + |c| + 1) / (-a)) := by
        apply mul_le_mul_of_nonpos_left hxbig ha'.le
      linarith
    have hquad : a * x ^ 2 + |b| * x + |c| = x * (a * x + |b|) + |c| := by
      ring
    have hneg : a * x + |b| ≤ -|c| - 1 := by linarith
    have hstep : x * (a * x + |b|) + |c| ≤ -x + |c| := by
      have hmul : x * (a * x + |b|) ≤ x * (-|c| - 1) := mul_le_mul_of_nonneg_left hneg hx.le
      have hdrop : -x * |c| ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg
        · linarith
        · exact abs_nonneg c
      linarith
    have hxgt : |c| < x := by
      have h1 : |c| + 1 ≤ |b| + |c| + 1 := by linarith [abs_nonneg b]
      have hx1 : |b| + |c| + 1 ≤ x := by
        apply le_mul_of_one_le_right (by positivity)
        linarith [inv_nonneg.mpr hna.le]
      linarith
    have hupper : a * x ^ 2 + b * x + c ≤ a * x ^ 2 + |b| * x + |c| := by
      have hb : b * x ≤ |b| * x := by
        have hle : b * x ≤ |b * x| := le_abs_self (b * x)
        rwa [abs_mul, abs_of_pos hx] at hle
      have hc : c ≤ |c| := le_abs_self c
      linarith
    linarith


-- created on 2026-10-11
-- updated on 2026-10-17
