import Mathlib.MeasureTheory.Integral.Prod
import sympy.stats.policy_trajectory.continuous_action
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


/--
Integral against the continuous-action stage kernel:
`∫ z, f z ∂(stageK θ y) = ∫ u, π_θ(u | y) • ∫ ρ, f (ρ, y, u) ∂(reward (y, u)) du`.
Continuous-action counterpart of
`Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : DensityModel Θ S A}
  {f : ℝ × S × A → E}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (y : S) :
-- imply
  ∫ z, f z ∂(M.stageK θ y) =
    ∫ u, M.policy.prob θ y u • ∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u))
      ∂ReferenceMeasure.measure := by
-- proof
  have := M.env.reward_markov
  have hπm : Measurable (M.policy.dens θ y) :=
    (M.policy.measurable_dens θ).comp measurable_prodMk_left
  unfold DensityModel.stageK
  rw [Kernel.map_apply _ (by fun_prop), integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [Kernel.prod_apply, Kernel.deterministic_apply]
  rw [id, Measure.dirac_prod, integral_map (f := fun x : S × A × ℝ => f (x.2.2, x.1, x.2.1))
    (by fun_prop) (hf.comp_measurable (by fun_prop)).aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd (f := fun x : A × ℝ => f (x.2, y, x.1))
    (Integrable.of_bound (hf.comp_measurable (by fun_prop)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _))]
  have hb : ∀ u, ‖∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u))‖ ≤ C := by
    intro u
    calc
      _ ≤ ∫ ρ, ‖f (ρ, y, u)‖ ∂(M.env.reward (y, u)) := norm_integral_le_integral_norm _
      _ ≤ ∫ ρ, C ∂(M.env.reward (y, u)) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const C) (Filter.Eventually.of_forall fun ρ => hC _)
      _ = C := by simp
  change ∫ u, ∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u)) ∂(M.policy.kernel θ y) = _
  have hker : M.policy.kernel θ y =
      (ReferenceMeasure.measure : Measure A).withDensity (M.policy.dens θ y) := by
    rw [DensityPolicy.kernel, Kernel.withDensity_apply _ (M.policy.measurable_dens θ)]
    rfl
  rw [hker, integral_withDensity_eq_integral_toReal_smul hπm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext u
  rw [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ y u)]


-- created on 2026-10-20
