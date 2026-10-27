import Mathlib.Analysis.Calculus.Gradient.Basic
import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
set_option maxHeartbeats 400000


/--
Baseline cancellation for continuous REINFORCE: replacing the discounted return
`∑' k, γ ^ k * r[t + k]` by the Vkd temporal-difference residual series
`∑' k, γ ^ k * (r[t + k] + γ * Vkd(s[t + k + 1]) - Vkd(s[t + k]))` does not change the
score-weighted path integral (telescoping + zero expected score).
Continuous-action counterpart of the `key` step in
`Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Ico.advantage`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
    ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
      M.Vkd θ γ (s (t + k) ω))) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  classical
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ x, |M.Vkd θ γ x| ≤ B :=
    ⟨(1 - γ)⁻¹ * |M.env.R|, fun x => by
      simpa [Real.norm_eq_abs] using NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ x⟩
  refine tsum_congr fun t => congrArg (fun z => γ ^ t • z) ?_
  have h₉ : ∀ᵐ ω ∂(M θ), ∑' k, γ ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
      M.Vkd θ γ (s (t + k) ω)) = (∑' k, γ ^ k * r (t + k) ω) - M.Vkd θ γ (s t ω) := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω hr
    have hb : ∀ k, |M.Vkd θ γ (s k ω)| ≤ B := fun k => hBd _
    set b : ℕ → ℝ := fun k => γ ^ k * M.Vkd θ γ (s (t + k) ω) with hbd
    have hlim : Tendsto b atTop (𝓝 0) :=
      Eq_0.Lim.of.LtAbs.GtInftySup (x := fun k => M.Vkd θ γ (s (t + k) ω))
        (by simpa [abs_of_nonneg h₀.1] using h₀.2) ⟨B, by rintro _ ⟨k, rfl⟩; exact hb (t + k)⟩
    have he : ∀ k, γ ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
        M.Vkd θ γ (s (t + k) ω)) = γ ^ k * r (t + k) ω + (b (k + 1) - b k) := fun k => by
      simp only [hbd]
      rw [show t + (k + 1) = t + k + 1 by omega]
      ring
    have hG : Summable fun k => γ ^ k * r (t + k) ω := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
        fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
    have hbs : Summable (fun k => b (k + 1) - b k) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (2 * B))
        fun k => ?_
      calc
        _ ≤ ‖b (k + 1)‖ + ‖b k‖ := norm_sub_le _ _
        _ ≤ γ ^ k * B + γ ^ k * B := by
          simp only [hbd]
          rw [norm_mul, norm_mul, norm_pow, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs,
            Real.norm_eq_abs]
          exact add_le_add (mul_le_mul (pow_le_pow_of_le_one h₀.1 h₀.2.le (Nat.le_succ k))
            (hb _) (abs_nonneg _) (pow_nonneg h₀.1 k)) (mul_le_mul_of_nonneg_left (hb _) (pow_nonneg h₀.1 k))
        _ = γ ^ k * (2 * B) := by ring
    have hbsum : ∑' k, (b (k + 1) - b k) = - b 0 := by
      refine tendsto_nhds_unique hbs.hasSum.tendsto_sum_nat ?_
      simp_rw [Finset.sum_range_sub]
      simpa using hlim.sub_const (b 0)
    simp_rw [he]
    rw [hG.tsum_add hbs, hbsum]
    simp only [hbd, pow_zero, one_mul, add_zero]
    ring
  have hmeasV : Measurable (M.Vkd θ γ) := Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ γ
  have hscore_sm : StronglyMeasurable fun ω =>
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ :=
    hφ.comp_measurable
      ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
        (Random.Measurable.of.All_Eq.snd.snd h₁ t))
  have hIntG : Integrable (fun ω => (∑' k, γ ^ k * r (t + k) ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ) (M θ) := by
    refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R| * Ms) ?_ ?_
    ·
      exact ((Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)).stronglyMeasurable.smul
        hscore_sm).aestronglyMeasurable
    ·
      filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω hr
      rw [norm_smul]
      have hret : ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
        tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|) fun k => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
          exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
      exact mul_le_mul hret (hMs _ _) (norm_nonneg _) ((norm_nonneg _).trans hret)
  have hIntV : Integrable (fun ω => M.Vkd θ γ (s t ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ) (M θ) := by
    refine Integrable.of_bound (C := B * Ms) ?_ ?_
    ·
      exact ((hmeasV.comp (Random.Measurable.of.All_Eq.snd.fst h₁ t)).stronglyMeasurable.smul
        hscore_sm).aestronglyMeasurable
    ·
      filter_upwards with ω
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hBd _) (hMs _ _) (norm_nonneg _)
        ((abs_nonneg (M.Vkd θ γ (s t ω))).trans (hBd _))
  symm
  calc
    _ = ∫ ω, ((∑' k, γ ^ k * r (t + k) ω) - M.Vkd θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
      integral_congr_ae (h₉.mono fun ω h => by dsimp only; rw [h])
    _ = (∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) -
        ∫ ω, M.Vkd θ γ (s t ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      simp_rw [sub_smul]
      exact integral_sub hIntG hIntV
    _ = _ := by
      have hz := Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
        (M := M) (θ := θ) (r := r) (s := s) (a := a) (g := g) (C := B) (B := Ms)
        h₁ h₂ h₃ h₄ (M.Vkd θ γ) hmeasV (fun y => by
          simpa [Real.norm_eq_abs] using hBd y) hφ hMs t
      rw [hz, sub_zero]


-- created on 2026-10-20
