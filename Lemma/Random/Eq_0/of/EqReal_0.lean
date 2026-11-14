import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
An event of real probability `0` is null: `(M θ).real B = 0 → M θ B = 0`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {B : Set (ℕ → ℝ × 𝒮 × 𝒜)}
  {θ : Θ}
-- given
  (h : (M θ).real B = 0) :
-- imply
  M θ B = 0 :=
-- proof
  (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h


-- created on 2026-10-07
-- updated on 2026-11-14
