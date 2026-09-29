import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


/--
For \(|e|<1\), the polar denominator \(1-e\cos x\) is positive.
-/
@[main]
private lemma main
  {e : ℝ}
-- given
  (he₀ : -1 < e)
  (he₁ : e < 1)
  (x : ℝ) :
-- imply
  1 - e * Real.cos x > 0 := by
-- proof
  have h₀ : |e * Real.cos x| ≤ |e| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
  have h₁ : |e| < 1 := abs_lt.mpr ⟨he₀, he₁⟩
  linarith [le_abs_self (e * Real.cos x)]


-- created on 2026-09-29