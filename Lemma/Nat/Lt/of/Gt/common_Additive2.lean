import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y α β l : ℝ}
-- given
  (hα : α > 0)
  (hβ : β > 0)
  (hl : l ∈ Set.Icc 0 1)
  (h : |x - y| > 0) :
-- imply
  |(x + (l * x + (1 - l) * y) * α) / (1 + α) - (y + (l * x + (1 - l) * y) * β) / (1 + β)| < |x - y| := by
-- proof
  obtain ⟨hl₀, hl₁⟩ := hl
  have h₁ : (1 : ℝ) + α ≠ 0 := by positivity
  have h₂ : (1 : ℝ) + β ≠ 0 := by positivity
  have key : (x + (l * x + (1 - l) * y) * α) / (1 + α) - (y + (l * x + (1 - l) * y) * β) / (1 + β) =
      (1 + β + α * l - β * l) / ((1 + α) * (1 + β)) * (x - y) := by
    field_simp
    ring
  have hd : (1 + α) * (1 + β) > 0 := by positivity
  have hc : |(1 + β + α * l - β * l) / ((1 + α) * (1 + β))| < 1 := by
    rw [abs_div, abs_of_pos hd, div_lt_one hd, abs_lt]
    constructor
    · nlinarith [mul_pos hα hβ, mul_nonneg hβ.le (sub_nonneg.mpr hl₁), mul_nonneg hα.le hl₀]
    · nlinarith [mul_pos hα hβ, mul_nonneg hα.le (sub_nonneg.mpr hl₁), mul_nonneg hβ.le hl₀]
  rw [key, abs_mul]
  calc _ < 1 * |x - y| := mul_lt_mul_of_pos_right hc h
    _ = |x - y| := one_mul _


-- created on 2019-07-27
