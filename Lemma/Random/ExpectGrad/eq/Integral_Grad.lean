import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Theorem.Dynamics.PolicyTrajectory.ContinuousAction
import Def.Analysis.Calculus.Gradient.Operators.Part2
open MeasureTheory PolicyGradient PolicyGradient.DensityModel Random Measure


/--
Path-binder Expect of `∇[θ] (V θ (s n))` equals the Bochner integral of the same observable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {θ : Θ} {n : ℕ}
  {V : Θ → 𝒮 → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮} [PSpace (M θ) (AsPathRV.path s)] :
-- imply
  𝔼[s : M θ](∇[θ] (V θ (s n))) =
    ∫ ω, ∇[θ] (V θ (s n ω)) ∂(M θ) := by
-- proof
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun path : ℕ → 𝒮 ↦ ∇[θ] (V θ (path n)))
  apply (StronglyMeasurable.comp_measurable
    (f := fun x : 𝒮 ↦ ∇[θ] (V θ x))
    StronglyMeasurable.of_discrete
    (measurable_pi_apply n)).aestronglyMeasurable


-- created on 2026-10-21
-- updated on 2026-11-14
