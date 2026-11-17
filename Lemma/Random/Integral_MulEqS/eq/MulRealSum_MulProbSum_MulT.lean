import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.Norm.le.Sum_Norm
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable_Eq12
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


private lemma w0
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (f : 𝒮 → ℝ)
  (y : 𝒮) :
-- imply
  ∫ z, M.Kf θ (fun z => f z.2.1) 0 z ∂(M.stageK θ y) = f y := by
-- proof
  rw [show M.Kf θ (fun z => f z.2.1) 0 = fun z => f z.2.1 from funext fun z => rfl]
  have hmap : (M.stageK θ).map (fun z => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    apply Kernel.fst_prod
  rw [← integral_map measurable_snd.fst.aemeasurable
    (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable]
  rw [← Kernel.map_apply (M.stageK θ) (by fun_prop) y, hmap,
    Kernel.deterministic_apply measurable_id, id, integral_dirac]

/--
`𝔼[1{s[t] = x} * f(s[t+1])] = ℙ(s[t] = x) * ∫ u, π_θ(u | x) * ∫ y, f y ∂T(x, u) ∂μ`
in the continuous-action trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (sₜ : 𝒮)
  (f : 𝒮 → ℝ) :
-- imply
  ∫ ω, (if s t ω = sₜ then (1:ℝ) else 0) * f (s (t + 1) ω) ∂(M.traj θ) =
    (M.traj θ).real (s t ⁻¹' {sₜ}) *
      ∫ u, M.π[θ] sₜ u * (∫ y, f y ∂(M.trans (sₜ, u))) ∂μ.measure := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have hf : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => f z.2.1) :=
    (StronglyMeasurable.of_discrete (f := f)).comp_measurable measurable_snd.fst
  have hC : ∀ z, ‖(fun z : ℝ × 𝒮 × 𝒜 => f z.2.1) z‖ ≤ ∑ y', ‖f y'‖ :=
    fun z => Norm.le.Sum_Norm f z.2.1
  have hK :=
    StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ 1
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hf hC (Real.StronglyMeasurable_Eq12 sₜ) Norm_1.le.One θ t 1).trans ?_
  refine (Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    h₀ (M := M) hK.1 hK.2 θ t sₜ).trans ?_
  congr 1
  show ∫ z, M.Kf θ (fun z => f z.2.1) (0 + 1) z ∂(M.stageK θ sₜ) = _
  rw [WAdd_1.eq.Integral_MulProbIntegral_TW.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hf hC θ 0 sₜ]
  congr 1
  funext u
  refine congrArg (fun inner => M.π[θ] sₜ u * inner) ?_
  congr 1
  funext y
  exact w0 (M := M) θ f y


-- created on 2026-10-07
-- updated on 2026-11-17