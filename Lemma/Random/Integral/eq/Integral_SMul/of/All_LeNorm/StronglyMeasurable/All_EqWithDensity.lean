import Lemma.Random.Eq_WithDensity_Pdf
import Mathlib.MeasureTheory.Integral.Prod
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Integral against the continuous-action stage kernel:
`∫ z, f z ∂(stageK θ y) = ∫ u, π_θ(u | y) • ∫ ρ, f (ρ, y, u) ∂(reward (y, u)) du`.
Continuous-action counterpart of
`Random.Integral.eq.Sum_SMul.of.All_LeNorm.StronglyMeasurable`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℰ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (y : 𝒮) :
-- imply
  ∫ z, f z ∂(M.stageK θ y) =
    ∫ u, M.π θ y u • ∫ ρ, f (ρ, y, u) ∂(M.reward (y, u) : Measure ℝ)
      ∂μ.measure := by
-- proof
  have hπm : Measurable (M.pdf θ y) :=
    (M.measurable_pdf θ).comp measurable_prodMk_left
  unfold Model.stageK
  rw [Kernel.map_apply _ (by fun_prop), integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [Kernel.prod_apply, Kernel.deterministic_apply]
  rw [id, Measure.dirac_prod, integral_map (f := fun x : 𝒮 × 𝒜 × ℝ => f (x.2.2, x.1, x.2.1))
    (by fun_prop) (hf.comp_measurable (by fun_prop)).aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd (f := fun x : 𝒜 × ℝ => f (x.2, y, x.1))
    (Integrable.of_bound (hf.comp_measurable (by fun_prop)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _))]
  have hb : ∀ u, ‖∫ ρ, f (ρ, y, u) ∂(M.reward (y, u) : Measure ℝ)‖ ≤ C := by
    intro u
    calc
      _ ≤ ∫ ρ, ‖f (ρ, y, u)‖ ∂(M.reward (y, u) : Measure ℝ) := norm_integral_le_integral_norm _
      _ ≤ ∫ ρ, C ∂(M.reward (y, u) : Measure ℝ) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (integrable_const C) (Filter.Eventually.of_forall fun ρ => hC _)
      _ = C := by simp
  change ∫ u, ∫ ρ, f (ρ, y, u) ∂(M.reward (y, u) : Measure ℝ) ∂(M.kernel θ y) = _
  have hker : M.kernel θ y =
      ReferenceMeasure.measure.withDensity (M.pdf θ y) :=
    Eq_WithDensity_Pdf (M := M) θ y
  rw [hker, integral_withDensity_eq_integral_toReal_smul hπm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext u
  simp [Policy.pdf]
  exact congrArg
    (fun r : ℝ => r • ∫ ρ, f (ρ, y, u) ∂(M.reward (y, u) : Measure ℝ))
    (ENNReal.toReal_ofReal (hStoch.nonneg θ y u))


-- created on 2026-10-20
-- updated on 2026-11-17