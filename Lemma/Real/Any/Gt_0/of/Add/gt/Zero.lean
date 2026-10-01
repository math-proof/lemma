import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₁ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x, a * x ^ 2 + b * x + c > 0 := by
-- proof
  by_cases h₀ : a = 0
  · subst h₀
    have hb : b ≠ 0 := by
      rintro rfl
      linarith
    have e : b * ((1 - c) / b) = 1 - c := by field_simp
    refine ⟨(1 - c) / b, ?_⟩
    rw [zero_mul, zero_add, e]
    linarith
  · rcases lt_or_gt_of_ne h₀ with ha | ha
    · have ha' : a ≠ 0 := ha.ne
      have e : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = -(b ^ 2 - 4 * a * c) / (4 * a) := by
        field_simp
        ring
      refine ⟨-b / (2 * a), ?_⟩
      rw [e]
      exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact ⟨1 + (|b| + |c| + 1) / a, by
        have hq : 0 ≤ (|b| + |c| + 1) / a := div_nonneg (by positivity) (by linarith)
        have e : a * ((|b| + |c| + 1) / a) = |b| + |c| + 1 := by field_simp
        set X := 1 + (|b| + |c| + 1) / a with hXdef
        have hX1 : 1 ≤ X := by linarith
        have hX2 : a * X ≥ |b| + |c| + 1 := by rw [hXdef, mul_add, e]; linarith
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (sub_nonneg.mpr hX2), mul_le_mul_of_nonneg_right (neg_abs_le b) (by linarith : (0 : ℝ) ≤ X),
          mul_nonneg (sub_nonneg.mpr hX1) (by positivity : (0 : ℝ) ≤ |c| + 1), neg_abs_le c]⟩


-- created on 2026-09-27
