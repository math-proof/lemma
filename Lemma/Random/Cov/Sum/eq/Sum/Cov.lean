import Mathlib.Probability.Moments.Covariance
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsFiniteMeasure π]
  {x : ι → Ω → ℝ} {y : Ω → ℝ} [Fintype ι]
-- given
  (h₀ : ∀ i, MemLp (x i) 2 π)
  (h₁ : MemLp y 2 π) :
-- imply
  covariance (fun ω => ∑ i, x i ω) y π = ∑ i, covariance (x i) y π :=
-- proof
  covariance_fun_sum_left h₀ h₁


-- created on 2023-04-19
-- updated on 2026-10-17
