import Mathlib.Probability.Moments.Variance
import Lemma.Random.Var.eq.Integral
open MeasureTheory ProbabilityTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → ℝ}
  {μ σ k : ℝ}
-- given
  [PSpace π x]
  (h₀ : MemLp x 2 π)
  (h₁ : π[x] = μ)
  (h₂ : 𝕍𝕒𝕣 π x = σ ^ 2)
  (h₃ : 0 < k)
  (h₄ : 0 < σ) :
-- imply
  π.real {ω | k * σ ≤ |x ω - μ|} ≤ 1 / k ^ 2 := by
-- proof
  have hV : variance x π = σ ^ 2 := by
    rw [variance_eq_integral (PSpace.aemeasurable (x := x)), ← Var.eq.Integral, h₂]
  have hdiv : σ ^ 2 / (k * σ) ^ 2 = 1 / k ^ 2 := by
    field_simp [h₃.ne', h₄.ne']
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  simpa [measureReal_def, hV, h₁, hdiv] using meas_ge_le_variance_div_sq (μ := π) h₀ (mul_pos h₃ h₄)


-- created on 2023-04-18
-- updated on 2026-10-17
