import Syntax.Order.Sup
import Lemma.Random.Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Filter Random Real
set_option maxHeartbeats 600000


/--
Infinite unroll of the continuous path policy-gradient identity:
`∫ ∇Vkd ∂init = ∑' t, γ ^ t • ∫ Qkd(s[t], a[t]) • ∇log π ∂(M θ)`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂M.env.init =
    ∑' t, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  classical
  have := M.env.init_prob
  have := M.env.trans_markov
  have hgrad : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u :=
    fun θ x u => by simpa [gradient, LinearIsometryEquiv.norm_map] using h₃ θ x u
  have hsup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞ :=
    ⟨Cg, by rintro _ ⟨x, rfl⟩; exact h₅ x⟩
  obtain ⟨C, hC⟩ :=
    GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ hgrad h₄ hsup h₀ hπ
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.Vkd θ γ y) θ‖ ≤ C := fun y => by
    have h := hC ⟨(θ, y), rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hVfd := fun y =>
    HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ hgrad h₄ hsup h₀ hπ y θ
  have hgm : StronglyMeasurable (fun y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ' γ)
      (fun y => (hVfd y).differentiableAt)
  have hstep := fun t =>
    Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs t
  have hfin : ∀ n,
      ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂M.env.init =
        ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
        γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_smul, zero_add]
      rw [Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁]
    | succ n ih =>
      have hrem := hstep n
      calc
        _ = ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
              fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
            γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)) := ih
        _ = ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
              fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
            γ ^ n • (∫ ω, M.Qkd θ γ (s n ω) (a n ω) •
              fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s n ω) (a n ω))) θ ∂(M θ) +
            γ • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (n + 1)))) := by
          rw [hrem]
        _ = ∑ t ∈ Finset.range (n + 1), γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
              fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
            γ ^ (n + 1) • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (n + 1))) := by
          rw [smul_add, smul_smul, Finset.sum_range_succ, pow_succ' γ n, mul_comm γ (γ ^ n),
            add_assoc]
  have hbd : ∀ n, ‖∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n))‖ ≤ C := fun n => by
    have : IsProbabilityMeasure ((M θ).map (s n)) := inferInstance
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hCb)).trans_eq (by simp)
  have hγ : |γ| < 1 := by rw [abs_of_nonneg h₀.1]; exact h₀.2
  have htend₀ :
      Tendsto (fun n => γ ^ n *
          ‖∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n))‖) atTop (𝓝 0) :=
    Eq_0.Lim.of.LtAbs.GtInftySup hγ
      ⟨C, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (hbd n)⟩
  have htend :
      Tendsto (fun n => γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine htend₀.congr fun n => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
  -- summable of the Q-score series
  have hQsum :
      Summable fun t => γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    -- bound via NormQ / Ms; use crude BQ * Ms
    set BQ : ℝ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)
    have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BQ * Ms)
    refine Summable.of_norm_bounded hs fun t => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    -- ‖∫ Q•score‖ ≤ ∫ ‖Q•score‖ ≤ BQ * Ms
    have : IsProbabilityMeasure (M θ) := inferInstance
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (integrable_const (BQ * Ms)) ?_).trans_eq (by simp)
    filter_upwards with ω
    rw [norm_smul]
    have hQ : ‖M.Qkd θ γ (s t ω) (a t ω)‖ ≤ BQ := by
      have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (s t ω, a t ω))
        (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y)
      unfold DensityModel.Qkd
      refine (norm_add_le _ _).trans (add_le_add (NormRkd.le.Abs_R (M := M) _ _) ?_)
      rw [norm_mul, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa using h) h₀.1
    exact mul_le_mul hQ (hMs _ _) (norm_nonneg _) ((norm_nonneg _).trans hQ)
  have hleft :
      Tendsto (fun n =>
        ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
        γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)))
        atTop (𝓝 (∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂M.env.init)) :=
    tendsto_const_nhds.congr fun n => hfin n
  have hsumtend := hQsum.hasSum.tendsto_sum_nat.add htend
  rw [add_zero] at hsumtend
  exact tendsto_nhds_unique hleft hsumtend


-- created on 2026-10-20
