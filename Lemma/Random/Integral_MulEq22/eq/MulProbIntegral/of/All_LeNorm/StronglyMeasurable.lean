import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`∫ z, 1{z.a = u} * g z ∂(stageK θ x) = π_θ(u | x) * μ({u}) * ∫ ρ, g (ρ, x, u) ∂(reward (x, u))`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {g : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (h₀ : StronglyMeasurable g)
  (h₁ : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  ∫ z, (if z.2.2 = aₜ then (1:ℝ) else 0) * g z ∂(M.stageK θ sₜ) =
    M.π[θ] sₜ aₜ * μ.measure.real {aₜ} *
      ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ)) := by
-- proof
  have hm : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => (if z.2.2 = aₜ then (1:ℝ) else 0) * g z) :=
    (Measurable.ite (measurable_snd.snd (measurableSet_singleton aₜ))
      measurable_const measurable_const).stronglyMeasurable.mul h₀
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) hm
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = aₜ)) h₁) θ]
  have hite : ∀ v,
      ∫ ρ, (if v = aₜ then (1:ℝ) else 0) * g (ρ, sₜ, v) ∂(M.reward (sₜ, v)) =
        (if v = aₜ then (1:ℝ) else 0) * ∫ ρ, g (ρ, sₜ, v) ∂(M.reward (sₜ, v)) := by
    intro v
    rw [integral_const_mul (if v = aₜ then (1:ℝ) else 0) (fun ρ => g (ρ, sₜ, v))]
  dsimp only
  conv =>
    lhs
    arg 2
    ext v
    rw [hite v]
    rw [smul_eq_mul]
  have hfun :
    (fun v => M.π[θ] sₜ v *
      ((if v = aₜ then (1:ℝ) else 0) * ∫ ρ, g (ρ, sₜ, v) ∂(M.reward (sₜ, v)))) =
    Set.indicator {aₜ}
      (fun _ => M.π[θ] sₜ aₜ * ∫ ρ, g (ρ, sₜ, aₜ) ∂(M.reward (sₜ, aₜ))) := by
    funext v
    if h : v = aₜ then
      simp [h, Set.indicator]
    else
      simp [h, Set.indicator]
  rw [hfun, integral_indicator (measurableSet_singleton aₜ), MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_left_comm, ← mul_assoc]


-- created on 2026-10-07
-- updated on 2026-11-16