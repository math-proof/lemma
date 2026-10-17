import Mathlib.Probability.Moments.Variance
import sympy.stats.variance
import Lemma.Random.Var.eq.Integral
import Lemma.Random.Cov.eq.Integral
import sympy.Basic
open MeasureTheory ProbabilityTheory Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {x y : Ω → ℝ}
-- given
  [PSpace π x] [PSpace π y] [PSpace π (fun ω => x ω + y ω)]
  (h₀ : MemLp x 2 π)
  (h₁ : MemLp y 2 π) :
-- imply
  𝕍𝕒𝕣 π (fun ω => x ω + y ω) =
    𝕍𝕒𝕣 π x + ℂ𝕠𝕧 π x y + ℂ𝕠𝕧 π y x + 𝕍𝕒𝕣 π y := by
-- proof
  have hx : AEMeasurable x π := PSpace.aemeasurable
  have hy : AEMeasurable y π := PSpace.aemeasurable
  have hz : AEMeasurable (fun ω => x ω + y ω) π := PSpace.aemeasurable
  rw [Var.eq.Integral, Var.eq.Integral, Var.eq.Integral, Cov.eq.Integral, Cov.eq.Integral,
    ← variance_eq_integral hx, ← variance_eq_integral hy, ← variance_eq_integral hz,
    ← covariance, ← covariance, variance_fun_add h₀ h₁, covariance_comm (X := y) (Y := x)]
  ring


-- created on 2023-04-19
-- updated on 2026-10-17
