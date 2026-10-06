import Mathlib.Analysis.Real.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Icc (-1) 1)
  (hy : y ∈ Set.Ico (-1) 1)
  (hxy : x < y) :
-- imply
  y * Real.sqrt (1 - x ^ 2) > x * Real.sqrt (1 - y ^ 2) := by
-- proof
  obtain ⟨hx1, _⟩ := Set.mem_Icc.mp hx
  obtain ⟨hy1, hy2⟩ := Set.mem_Ico.mp hy
  by_cases hx0 : 0 ≤ x
  · -- 0 ≤ x < y < 1
    have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
    have h1y : 0 ≤ 1 - y ^ 2 := by nlinarith
    have hypos : 0 < y := by linarith
    set a := y * Real.sqrt (1 - x ^ 2) with ha_def
    set b := x * Real.sqrt (1 - y ^ 2) with hb_def
    have ha0 : 0 < a := by
      rw [ha_def]
      exact mul_pos hypos (Real.sqrt_pos.mpr (by nlinarith))
    have hb0 : 0 ≤ b := by
      rw [hb_def]
      exact mul_nonneg hx0 (Real.sqrt_nonneg _)
    have hsq : a ^ 2 > b ^ 2 := by
      rw [ha_def, hb_def, mul_pow, Real.sq_sqrt h1x, mul_pow, Real.sq_sqrt h1y]
      nlinarith
    nlinarith [sq_nonneg (a - b)]
  · -- x < 0
    have hxn : x < 0 := by linarith
    by_cases hy0 : 0 ≤ y
    · have hsqrt : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
      have hneg : x * Real.sqrt (1 - y ^ 2) < 0 := mul_neg_of_neg_of_pos hxn hsqrt
      have hnonneg : 0 ≤ y * Real.sqrt (1 - x ^ 2) :=
        mul_nonneg hy0 (Real.sqrt_nonneg _)
      linarith
    · -- x < y < 0
      have hyn : y < 0 := by linarith
      by_cases hxm : -1 < x
      · have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
        have h1y : 0 ≤ 1 - y ^ 2 := by nlinarith
        set a := y * Real.sqrt (1 - x ^ 2) with ha_def
        set b := x * Real.sqrt (1 - y ^ 2) with hb_def
        have ha0 : a ≤ 0 := by
          rw [ha_def]
          exact mul_nonpos_of_nonpos_of_nonneg hyn.le (Real.sqrt_nonneg _)
        have hb0 : b < 0 := by
          rw [hb_def]
          exact mul_neg_of_neg_of_pos hxn (Real.sqrt_pos.mpr (by nlinarith))
        have hsq : a ^ 2 < b ^ 2 := by
          rw [ha_def, hb_def, mul_pow, Real.sq_sqrt h1x, mul_pow, Real.sq_sqrt h1y]
          nlinarith
        nlinarith [sq_nonneg (a - b)]
      · have hxe : x = -1 := by linarith
        rw [hxe]
        have hsqrt : 0 < Real.sqrt (1 - y ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
        have hz : Real.sqrt (1 - (-1 : ℝ) ^ 2) = 0 := by simp
        rw [hz]
        simpa using hsqrt


-- created on 2020-11-29
