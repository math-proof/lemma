import Lemma.Random.Integral_SMul.eq.Zero.of.Le.In_Ico.All_EqWithDensity
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real
set_option maxHeartbeats 800000


private lemma integral_delta_smul_eq_zero
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A ↦ M.policy.prob θ z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (ψ : S → A → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
  ∫ ω, (r (n + 1) ω + γ * M.Vkd θ γ (s (n + 1 + 1) ω) - M.Vkd θ γ (s (n + 1) ω)) •
    ψ (s t ω) (a t ω) ∂(M θ) = 0 := by
  obtain ⟨Ms, hMs⟩ := hMs
  refine ContinuousLinearMap.ext fun v => ?_
  have hφ : StronglyMeasurable (Function.uncurry fun y u => (ψ y u) v) :=
    (continuous_eval_const v).comp_stronglyMeasurable hψ
  have hφb : ∃ Ms' : ℝ, ∀ y u, ‖(ψ y u) v‖ ≤ Ms' :=
    ⟨Ms * ‖v‖, fun y u =>
      (ContinuousLinearMap.le_opNorm (ψ y u) v).trans
        (mul_le_mul_of_nonneg_right (hMs y u) (norm_nonneg v))⟩
  set Bδ : ℝ := (3 / (1 - γ) - 1) * |M.env.R|
  have hInt :
      Integrable (fun ω =>
        (r (n + 1) ω + γ * M.Vkd θ γ (s (n + 1 + 1) ω) - M.Vkd θ γ (s (n + 1) ω)) •
          ψ (s t ω) (a t ω)) (M θ) := by
    refine Integrable.of_bound
      ((((Random.Measurable.of.All_Eq.fst h₁ (n + 1)).add
          (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
            (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1 + 1))).const_mul γ)).sub
        ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1)))).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (Bδ * Ms) ?_
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω hδ
    rw [norm_smul]
    have hB0 : 0 ≤ Bδ := by
      refine mul_nonneg ?_ (abs_nonneg _)
      refine sub_nonneg.2 ?_
      have hγ : 0 < 1 - γ := sub_pos.2 h₀.2
      exact (one_le_div₀ hγ).2 (by linarith [h₀.1, h₀.2])
    exact mul_le_mul (hδ _) (hMs _ _) (norm_nonneg _) hB0
  rw [ContinuousLinearMap.integral_apply hInt v]
  simp_rw [smul_apply, smul_eq_mul]
  exact Integral_SMul.eq.Zero.of.Le.In_Ico.All_EqWithDensity
    (M := M) t n h₀ h₁ hπ h₂ θ (fun y u => (ψ y u) v) hφ hφb


/--
GAE reduction under the continuous-action path law:
`∫ ((∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])) = ∫ (δ[t] • ψ(s[t], a[t]))`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ c : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A ↦ M.policy.prob θ z.1 z.2))
  (θ : Θ)
  (h₂ : c ∈ Set.Ico 0 1)
  (t : ℕ)
  (ψ : S → A → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
    M.Vkd θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (r t ω + γ * M.Vkd θ γ (s (t + 1) ω) - M.Vkd θ γ (s t ω)) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  classical
  obtain ⟨Ms, hMs⟩ := hMs
  let F : ℕ → (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) - M.Vkd θ γ (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
      M.Vkd θ γ (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  set Bδ : ℝ := (3 / (1 - γ) - 1) * |M.env.R|
  have hB0 : 0 ≤ Bδ := by
    refine mul_nonneg ?_ (abs_nonneg _)
    refine sub_nonneg.2 ?_
    have hγ : 0 < 1 - γ := sub_pos.2 h₀.2
    exact (one_le_div₀ hγ).2 (by linarith [h₀.1, h₀.2])
  have hδm : ∀ k, Measurable fun ω =>
      r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) - M.Vkd θ γ (s (t + k) ω) := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
      (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))
  have hFi : ∀ k, Integrable (F k) (M θ) := fun k => by
    refine Integrable.of_bound
      (((hδm k).const_mul (c ^ k)).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (c ^ k * (Bδ * Ms)) ?_
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMs _ _) (norm_nonneg _) hB0
  have hFb : ∀ k, ∀ᵐ ω ∂(M θ), ‖F k ω‖ ≤ c ^ k * (Bδ * Ms) := fun k => by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMs _ _) (norm_nonneg _) hB0
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right (Bδ * Ms))
    calc
      _ ≤ ∫ _, c ^ k * (Bδ * Ms) ∂(M θ) :=
        integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * (Bδ * Ms) := by simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, k ≠ 0 → ∫ ω, F k ω ∂(M θ) = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := integral_delta_smul_eq_zero (M := M) t (t + k') h₀ h₁ hπ (Nat.le_add_right t k') θ ψ hψ ⟨Ms, hMs⟩
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.Vkd θ γ (s (t + k'.succ + 1) ω) -
        M.Vkd θ γ (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.Vkd θ γ (s (t + k' + 1 + 1) ω) - M.Vkd θ γ (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M θ) = ∫ ω, F 0 ω ∂(M θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
        M.Vkd θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico.All_EqWithDensity (M := M) h₀ h₁ θ] with ω h
    have hs : Summable (fun k => c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
        M.Vkd θ γ (s (t + k) ω))) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right Bδ)
        fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₂.1]
      exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg h₂.1 k)
    exact (hs.tsum_smul_const _).symm
  rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
  simp [F]


-- created on 2026-10-20
