import Lemma.Random.Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Filter Random Real


/--
Finite-horizon policy-gradient identity for a `DensityModel`: the series of
reward derivatives equals the truncated Q-score sum plus a `γ ^ n`-remainder
on `∇V0` under the time-`n` state law. The action value is the closed form
`rkd + γ * ∫ V0`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ < ∞)
  (n : ℕ) :
-- imply
  let S :=
    ∑ t ∈ Finset.range n,
      γ ^ t • ∫ ω, (M.rkd (s t ω) (a t ω) +
          γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (s t ω, a t ω))) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    S + γ ^ n • ∫ x, fderiv ℝ (fun θ => M.V0 θ γ x) θ ∂((M θ).map (s n)) := by
-- proof
  have hinit := Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ
  rw [
    TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ,
    ← hinit]
  induction n with
  | zero =>
    dsimp only
    simp
  | succ n ih =>
    dsimp only at ih ⊢
    have hstep :=
      Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs n
    rw [ih, Finset.sum_range_succ, hstep, smul_add, add_assoc]
    congr 1
    rw [smul_smul]
    have hpow : γ ^ n * γ = γ ^ (n + 1) := by
      rw [mul_comm, pow_succ']
    rw [hpow]


-- created on 2026-11-13
