import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
Bessel's correction for two i.i.d. samples: the unbiased sum of squared deviations from the
sample mean and the average squared deviation from the true mean have the same expectation `σ²`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x y : Ω → ℝ}
  {μ σ : ℝ}
-- given
  (h₀ : x ⟂ᵢ[π] y)
  (h₁ : π[x] = μ)
  (h₂ : π[y] = μ)
  (h₃ : variance x π = σ ^ 2)
  (h₄ : variance y π = σ ^ 2)
  (h₅ : MemLp x 2 π)
  (h₆ : MemLp y 2 π) :
-- imply
  ∫ ω, (x ω - (x ω + y ω) / 2) ^ 2 + (y ω - (x ω + y ω) / 2) ^ 2 ∂π =
    ∫ ω, ((x ω - μ) ^ 2 + (y ω - μ) ^ 2) / 2 ∂π := by
-- proof
  have hx : ∫ ω, (x ω - μ) ^ 2 ∂π = σ ^ 2 := by
    have hv := variance_eq_integral h₅.aemeasurable
    rw [h₁] at hv
    rw [← hv, h₃]
  have hy : ∫ ω, (y ω - μ) ^ 2 ∂π = σ ^ 2 := by
    have hv := variance_eq_integral h₆.aemeasurable
    rw [h₂] at hv
    rw [← hv, h₄]
  have hcov : ∫ ω, (x ω - μ) * (y ω - μ) ∂π = 0 := by
    have h := h₀.covariance_eq_zero h₅ h₆
    rw [covariance, h₁, h₂] at h
    apply h
  have hxμ : MemLp (fun ω => x ω - μ) 2 π := h₅.sub (memLp_const μ)
  have hyμ : MemLp (fun ω => y ω - μ) 2 π := h₆.sub (memLp_const μ)
  have hxy : ∫ ω, (x ω - y ω) ^ 2 ∂π = 2 * σ ^ 2 := by
    have hpoint : ∀ ω, (x ω - y ω) ^ 2 =
        (x ω - μ) ^ 2 + (y ω - μ) ^ 2 - 2 * ((x ω - μ) * (y ω - μ)) := by
      intro ω
      ring
    simp_rw [hpoint]
    rw [integral_sub, integral_add, hx, hy, integral_const_mul, hcov]
    · ring
    · apply hxμ.integrable_sq
    · apply hyμ.integrable_sq
    · apply hxμ.integrable_sq.add hyμ.integrable_sq
    · apply (hxμ.integrable_mul hyμ).const_mul
  have halg : ∀ ω, (x ω - (x ω + y ω) / 2) ^ 2 + (y ω - (x ω + y ω) / 2) ^ 2 =
      (x ω - y ω) ^ 2 / 2 := by
    intro ω
    ring
  simp_rw [halg]
  rw [integral_div, hxy, integral_div, integral_add hxμ.integrable_sq hyμ.integrable_sq, hx, hy]
  ring


-- created on 2023-10-08
-- updated on 2026-10-26
