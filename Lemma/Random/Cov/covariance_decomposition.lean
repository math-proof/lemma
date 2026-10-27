import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory


/--
Covariance pulls the second argument inside a conditional expectation on a σ-algebra that
makes the first argument measurable: `cov[X, Y] = cov[X, 𝔼[Y | m]]`.
-/
@[path]
private lemma main
  [mΩ : MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {m : MeasurableSpace Ω}
  {X Y : Ω → ℝ}
-- given
  (h₀ : m ≤ mΩ)
  (h₁ : MemLp X 2 π)
  (h₂ : MemLp Y 2 π)
  (h₃ : AEStronglyMeasurable[m] X π) :
-- imply
  covariance X Y π = covariance X (condExp m π Y) π := by
-- proof
  rw [covariance_eq_sub h₁ h₂, covariance_eq_sub h₁ (MemLp.condExp one_le_two h₂),
    integral_condExp (μ := π) h₀]
  congr 1
  exact (integral_condExp (μ := π) (f := X * Y) h₀).symm.trans
    (integral_congr_ae
      (condExp_mul_of_aestronglyMeasurable_left h₃ (h₁.integrable_mul h₂) (h₂.integrable one_le_two)))


-- created on 2023-04-09
-- updated on 2026-10-26
