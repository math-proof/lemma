import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real


/--
`∫ z, 1{z.a = u} * g z ∂(stageK θ x) = π_θ(u | x) * μ({u}) * ∫ ρ, g (ρ, x, u) ∂(reward (x, u))`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜] [DecidableEq 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {g : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
-- given
  (h₀ : StronglyMeasurable g)
  (h₁ : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  ∫ z, (if z.2.2 = u then (1:ℝ) else 0) * g z ∂(M.stageK θ x) =
    M.policy.prob θ x u * μ.measure.real {u} *
      ∫ ρ, g (ρ, x, u) ∂(M.env.reward (x, u)) := by
-- proof
  have hm : StronglyMeasurable
    (fun z : ℝ × 𝒮 × 𝒜 => (if z.2.2 = u then (1:ℝ) else 0) * g z) :=
    (Measurable.ite (measurable_snd.snd (measurableSet_singleton u))
      measurable_const measurable_const).stronglyMeasurable.mul h₀
  rw [Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity (M := M) hm
    (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.2 = u)) h₁) θ]
  have hite : ∀ v,
      ∫ ρ, (if v = u then (1:ℝ) else 0) * g (ρ, x, v) ∂(M.env.reward (x, v)) =
        (if v = u then (1:ℝ) else 0) * ∫ ρ, g (ρ, x, v) ∂(M.env.reward (x, v)) := by
    intro v
    rw [integral_const_mul (if v = u then (1:ℝ) else 0) (fun ρ => g (ρ, x, v))]
  dsimp only
  conv =>
    lhs
    arg 2
    ext v
    rw [hite v]
    rw [smul_eq_mul]
  have hfun :
    (fun v => M.policy.prob θ x v *
      ((if v = u then (1:ℝ) else 0) * ∫ ρ, g (ρ, x, v) ∂(M.env.reward (x, v)))) =
    Set.indicator {u}
      (fun _ => M.policy.prob θ x u * ∫ ρ, g (ρ, x, u) ∂(M.env.reward (x, u))) := by
    funext v
    if h : v = u then
      simp [h, Set.indicator]
    else
      simp [h, Set.indicator]
  rw [hfun, integral_indicator (measurableSet_singleton u), MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_left_comm, ← mul_assoc]


-- created on 2026-10-07
-- updated on 2026-11-14
