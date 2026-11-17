import Lemma.Random.Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real
set_option maxHeartbeats 900000


/--
The init-average of `V0` is the discounted expected path return:
`∫ V0 θ γ ∂init = ∑' t, γ ^ t * ∫ r[t]`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (θ : Θ) :
-- imply
  ∫ x, M.V0 θ γ x ∂M.init.toMeasure =
    ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ) := by
-- proof
  have hW : ∀ t, ∫ ω, r t ω ∂(M.traj θ) =
    ∫ x, M.Wkd θ t x ∂M.init.toMeasure := fun t =>
    Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity (M := M) h₁ θ t
  simp_rw [hW]
  have hmeas : ∀ t, Measurable (M.Wkd θ t) := fun t =>
    Measurable_Wkd.of.All_Measurable_Prob hπ θ t
  have hbd : ∀ t x, ‖M.Wkd θ t x‖ ≤ |M.R| := fun t x =>
    NormWkd.le.Abs_R (M := M) θ t x
  have hri : ∀ t, Integrable (fun x => γ ^ t * M.Wkd θ t x) M.init.toMeasure :=
    fun t => by
      refine Integrable.of_bound ((hmeas t).const_mul (γ ^ t)).aestronglyMeasurable
        (γ ^ t * |M.R|) ?_
      filter_upwards with x
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hbd t x) (pow_nonneg h₀.1 t)
  have hsum_norm :
    Summable (fun t => ∫ x, ‖γ ^ t * M.Wkd θ t x‖ ∂M.init.toMeasure) := by
    refine Summable.of_nonneg_of_le
      (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.R|)
    calc
      _ ≤ ∫ _, γ ^ t * |M.R| ∂M.init.toMeasure :=
        integral_mono_ae (hri t).norm (integrable_const _)
          (Filter.Eventually.of_forall fun x => by
            change ‖γ ^ t * M.Wkd θ t x‖ ≤ γ ^ t * |M.R|
            rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
            exact mul_le_mul_of_nonneg_left (hbd t x) (pow_nonneg h₀.1 t))
      _ = γ ^ t * |M.R| := by
        have : IsProbabilityMeasure M.init.toMeasure := inferInstance
        rw [integral_const (μ := M.init.toMeasure), probReal_univ, one_smul]
  have hswap :
    ∫ x, ∑' t, γ ^ t * M.Wkd θ t x ∂M.init.toMeasure =
      ∑' t, ∫ x, γ ^ t * M.Wkd θ t x ∂M.init.toMeasure :=
    (integral_tsum_of_summable_integral_norm hri hsum_norm).symm
  have hV : (fun x => M.V0 θ γ x) =
    fun x => ∑' t, γ ^ t * M.Wkd θ t x := funext fun x => rfl
  rw [hV, hswap]
  refine tsum_congr fun t => ?_
  exact integral_const_mul _ _


-- created on 2026-10-20
-- updated on 2026-11-17