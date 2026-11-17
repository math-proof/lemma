import Def.Analysis.Calculus.Gradient.Operators.Part2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory PolicyGradient PolicyGradient.Model Random Real


private lemma W_bnd
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (y : 𝒮) :
-- imply
  ‖∫ z, M.Kf θ f j z ∂(M.stageK θ y)‖ ≤ C := by
-- proof
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall
      (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hC θ j).2)
  simpa using h

private lemma reward_int_bdd
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (hC : ∀ z, ‖f z‖ ≤ C)
  (y : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ‖∫ ρ, f (ρ, y, aₜ) ∂(M.reward (y, aₜ))‖ ≤ C := by
-- proof
  have h := norm_integral_le_of_norm_le_const (μ := M.reward (y, aₜ))
    (Filter.Eventually.of_forall fun ρ => hC (ρ, y, aₜ))
  simpa using h

private lemma measurable_integral_reward
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
-- given
  (hf : StronglyMeasurable f)
  (y : 𝒮) :
-- imply
  Measurable (fun u => ∫ ρ, f (ρ, y, u) ∂(M.reward (y, u))) := by
-- proof
  exact
    ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.rewardK)
      (f := fun p => f (p.2, p.1.1, p.1.2))
      (hf.comp_measurable (by fun_prop))).measurable).comp measurable_prodMk_left

private lemma measurable_integral_W
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ)
  (sₜ : 𝒮) :
-- imply
  Measurable (fun u =>
    ∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u))) := by
-- proof
  have hKf :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j
  have hΦ :
    StronglyMeasurable (fun y : 𝒮 => ∫ z, M.Kf θ f j z ∂(M.stageK θ y)) :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := M.stageK θ)
      (f := fun p => M.Kf θ f j p.2)
      (hKf.1.comp_measurable measurable_snd)
  exact
    ((StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK)
      (f := fun z => ∫ w, M.Kf θ f j w ∂(M.stageK θ z.2))
      (hΦ.comp_measurable measurable_snd)).measurable).comp
      measurable_prodMk_left

/--
If every `θ ↦ π_θ(u | x)` is differentiable with `‖fderiv π(u | x)‖ ≤ g x u`, where `g x` is integrable over the actions
with `∫ g x ≤ Cg`, and `‖f‖ ≤ Cf` with `f` strongly measurable (and `π` is jointly measurable in `(x, u)`), then
`θ ↦ ∫ z, Kf θ f j z ∂(stageK θ x)` is differentiable with derivative bounded by `(j + 1) * (Cg * Cf)`.
Continuous-action counterpart of
`Random.Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb`:
the finite action sum becomes an integral against the reference measure of `𝒜`, and `|𝒜| * Cp` becomes `Cg`.
This is the general-`f` form of
`Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {Cg : ℝ}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {Cf : ℝ}
-- given
  (h₀ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure ≤ Cg)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) ReferenceMeasure.measure)
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ Cf)
  (hCf : 0 ≤ Cf)
  (j : ℕ)
  (sₜ : 𝒮) :
-- imply
  Differentiable ℝ (fun θ => ∫ z, M.Kf θ f j z ∂(M.stageK θ sₜ)) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => ∫ z, M.Kf θ f j z ∂(M.stageK θ sₜ)) θ‖ ≤
      (j + 1) * (Cg * Cf) := by
-- proof
  let g : 𝒮 → 𝒜 → ℝ :=
    fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)
  have hBound : ∀ θ sₜ aₜ, ‖fderiv ℝ (fun θ => M.π[θ] sₜ aₜ) θ‖ ≤ g sₜ aₜ := by
    intro θ sₜ aₜ
    have : ‖∇[θ] M.π[θ] sₜ aₜ‖ ≤ g sₜ aₜ := by
      refine le_csSup ?_ ⟨θ, rfl⟩
      exact hBdd sₜ aₜ
    simpa [gradient, LinearIsometryEquiv.norm_map] using this
  have hInt : ∀ x, Integrable (g x) ReferenceMeasure.measure := by
    intro x
    exact hIntg x
  have hR : ∀ y, Cf * ∫ u, g y u ∂ReferenceMeasure.measure ≤ Cg * Cf := fun y => by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (h₂ y) hCf
  induction j generalizing sₜ with
  | zero =>
    have e : (fun θ => ∫ z, M.Kf θ f 0 z ∂(M.stageK θ sₜ)) =
        fun θ => ∫ u, M.π[θ] sₜ u *
          (∫ ρ, f (ρ, sₜ, u) ∂(M.reward (sₜ, u))) ∂ReferenceMeasure.measure :=
      funext fun θ => by
        change ∫ z, f z ∂(M.stageK θ sₜ) = _
        rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hf hC θ sₜ]
        simp [smul_eq_mul]
    rw [e]
    have hD := fun θ =>
      HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
        (ν := ReferenceMeasure.measure) (f := fun θ u => M.π[θ] sₜ u)
        (G := fun _ u => ∫ ρ, f (ρ, sₜ, u) ∂(M.reward (sₜ, u))) (g := g sₜ)
        (B₀ := Cf) (B₁ := 0)
        (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ sₜ)
        (fun θ u => hStoch.nonneg θ sₜ u) (fun θ => hStoch.integral_eq_one θ sₜ)
        (fun θ u => hBound θ sₜ u) (hInt sₜ)
        (fun _ => measurable_integral_reward (M := M) hf sₜ)
        (fun u => differentiable_const _)
        (fun _ u => reward_int_bdd (M := M) hC sₜ u)
        (fun θ u => by simp) θ
    have hW : ∀ θ, HasFDerivAt
      (fun θ => ∫ u, M.π[θ] sₜ u *
        (∫ ρ, f (ρ, sₜ, u) ∂(M.reward (sₜ, u))) ∂ReferenceMeasure.measure) _ θ :=
      fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv, Nat.cast_zero, zero_add, one_mul]
    linarith [(hD θ).2, hR sₜ]
  | succ j ih =>
    have e : (fun θ => ∫ z, M.Kf θ f (j + 1) z ∂(M.stageK θ sₜ)) =
        fun θ => ∫ u, M.π[θ] sₜ u *
          (∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u)))
          ∂ReferenceMeasure.measure :=
      funext fun θ =>
        WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hf hC θ j sₜ
    rw [e]
    have hT : ∀ θ, Measurable (fun u =>
        ∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u))) :=
      fun θ => measurable_integral_W (M := M) hf hC θ j sₜ
    have hI : ∀ u θ, HasFDerivAt
      (fun θ => ∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u)))
      (∫ y, fderiv ℝ (fun θ => ∫ z, M.Kf θ f j z ∂(M.stageK θ y)) θ
        ∂(M.trans (sₜ, u))) θ := fun u θ =>
      hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun θ y => ∫ z, M.Kf θ f j z ∂(M.stageK θ y))
        (F' := fun θ y =>
          fderiv ℝ (fun θ => ∫ z, M.Kf θ f j z ∂(M.stageK θ y)) θ)
        (s := Set.univ) (bound := fun _ => ((j : ℝ) + 1) * (Cg * Cf))
        Filter.univ_mem
        (Filter.Eventually.of_forall fun θ' =>
          (StronglyMeasurable.integral_kernel_prod_right' (κ := M.stageK θ')
            (f := fun p => M.Kf θ' f j p.2)
            ((StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
              (M := M) hf hC θ' j).1.comp_measurable measurable_snd)).aestronglyMeasurable)
        (Integrable.of_bound
          (StronglyMeasurable.integral_kernel_prod_right' (κ := M.stageK θ)
            (f := fun p => M.Kf θ f j p.2)
            ((StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
              (M := M) hf hC θ j).1.comp_measurable measurable_snd)).aestronglyMeasurable
          Cf (Filter.Eventually.of_forall fun y => W_bnd (M := M) hf hC θ j y))
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' =>
            (StronglyMeasurable.integral_kernel_prod_right' (κ := M.stageK θ')
              (f := fun p => M.Kf θ' f j p.2)
              ((StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
                (M := M) hf hC θ' j).1.comp_measurable measurable_snd)).measurable)
          (fun y => (ih y).1 θ)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y θ' _ => (ih y).2 θ')
        (integrable_const _)
        (Filter.Eventually.of_forall fun y θ' _ => ((ih y).1 θ').hasFDerivAt)
    have hg' : ∀ θ u, ‖fderiv ℝ (fun θ =>
        ∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u))) θ‖ ≤
        ((j : ℝ) + 1) * (Cg * Cf) := fun θ u => by
      rw [(hI u θ).fderiv]
      have h :=
        norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u))
          (Filter.Eventually.of_forall fun y => (ih y).2 θ)
      simpa using h
    have hgb : ∀ θ u, ‖∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y))
      ∂(M.trans (sₜ, u))‖ ≤ Cf := fun θ u => by
      have h :=
        norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u))
          (Filter.Eventually.of_forall fun y => W_bnd (M := M) hf hC θ j y)
      simpa using h
    have hD := fun θ =>
      HasFDerivAt.LeNorm.of.All_LeNormFderiv.All_LeNorm.All_Differentiable.All_Measurable.Integrable.All_LeNormFderiv.All_EqIntegral_1.All_Ge_0.All_Differentiable.All_Measurable
        (ν := ReferenceMeasure.measure) (f := fun θ u => M.π[θ] sₜ u)
        (G := fun θ u =>
          ∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u)))
        (g := g sₜ) (B₀ := Cf) (B₁ := ((j : ℝ) + 1) * (Cg * Cf))
        (fun θ => (h₀ θ).comp measurable_prodMk_left) (h₁ sₜ)
        (fun θ u => hStoch.nonneg θ sₜ u) (fun θ => hStoch.integral_eq_one θ sₜ)
        (fun θ u => hBound θ sₜ u) (hInt sₜ)
        hT (fun u θ => (hI u θ).differentiableAt) hgb hg' θ
    have hW : ∀ θ, HasFDerivAt (fun θ => ∫ u, M.π[θ] sₜ u *
        (∫ y, (∫ z, M.Kf θ f j z ∂(M.stageK θ y)) ∂(M.trans (sₜ, u)))
        ∂ReferenceMeasure.measure) _ θ := fun θ => (hD θ).1
    refine ⟨fun θ => (hW θ).differentiableAt, fun θ => ?_⟩
    rw [(hW θ).fderiv]
    push_cast
    linarith [(hD θ).2, hR sₜ]


-- created on 2026-11-13
-- updated on 2026-11-17
