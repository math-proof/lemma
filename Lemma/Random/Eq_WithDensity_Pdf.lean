import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
import Mathlib.Probability.Kernel.WithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
The policy kernel `M[x] θ` is the reference measure of `𝒜` with density `π_θ(· | x)`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  M[sₜ] θ =
    μ.measure.withDensity (M.pdf θ sₜ) := by
-- proof
  change M.kernel θ sₜ =
    μ.measure.withDensity (M.pdf θ sₜ)
  apply Kernel.withDensity_apply (Kernel.const 𝒮 (μ.measure : Measure 𝒜))
    (M.measurable_pdf θ)


-- created on 2026-11-16
-- updated on 2026-11-16
