import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Mathlib.MeasureTheory.Measure.WithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model PolicyGradient.DensityModel


/-- A finite-action policy kernel agrees with its counting-measure density-policy view. -/
private lemma kernel_eq_toDensityPolicy
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
-- given
  (p : Policy Θ 𝒮 𝒜)
  (θ : Θ) :
-- imply
  p.kernel θ = p.toDensityPolicy.kernel θ := by
-- proof
  refine Kernel.ext fun x => ?_
  have hL : p.kernel θ x = p.measure θ x := rfl
  have hmeas : Measurable (Function.uncurry (p.toDensityPolicy.dens θ)) :=
    p.toDensityPolicy.measurable_dens θ
  have hR : p.toDensityPolicy.kernel θ x =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (p.toDensityPolicy.dens θ x) := by
    rw [DensityPolicy.kernel, Kernel.withDensity_apply _ hmeas, Kernel.const_apply]
  rw [hL, hR, CountableMeasure.measure_eq_count, count_withDensity, Measure.sum_fintype]
  simp [Policy.measure, DensityPolicy.dens, Policy.toDensityPolicy]

/-- Stage kernels agree after `Model.toDensityModel`. -/
private lemma stageK_eq_toDensityModel
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
-- given
  (M : Model Θ 𝒮 𝒜)
  (θ : Θ) :
-- imply
  M.stageK θ = M.toDensityModel.stageK θ := by
-- proof
  unfold Model.stageK DensityModel.stageK Model.toDensityModel
  rw [kernel_eq_toDensityPolicy]

/-- Transition kernels of the stage chain agree after `Model.toDensityModel`. -/
private lemma K_eq_toDensityModel
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
-- given
  (M : Model Θ 𝒮 𝒜)
  (θ : Θ) :
-- imply
  M.K θ = M.toDensityModel.K θ := by
-- proof
  unfold Model.K DensityModel.K
  rw [stageK_eq_toDensityModel]
  congr 1

/-- History-dependent step kernels agree after `Model.toDensityModel`. -/
private lemma step_eq_toDensityModel
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
-- given
  (M : Model Θ 𝒮 𝒜)
  (θ : Θ)
  (n : ℕ) :
-- imply
  M.step θ n = M.toDensityModel.step θ n := by
-- proof
  unfold Model.step DensityModel.step
  rw [K_eq_toDensityModel]

/--
The Ionescu–Tulcea trajectory law of a finite-action `Model` agrees with that of
`M.toDensityModel` (counting-measure density policy, same environment).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : Model Θ 𝒮 𝒜}
  {θ : Θ} :
-- imply
  M.traj θ = M.toDensityModel.traj θ := by
-- proof
  unfold Model.traj DensityModel.traj
  simp only [Model.toDensityModel]
  rw [stageK_eq_toDensityModel]
  congr 1
  funext n
  simpa [Model.toDensityModel] using step_eq_toDensityModel M θ n


-- created on 2026-11-11
