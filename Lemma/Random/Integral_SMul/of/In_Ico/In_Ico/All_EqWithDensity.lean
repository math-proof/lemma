import Lemma.Random.Integral_SMul.eq.Zero.of.Le.In_Ico.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Theorem.Function
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real
set_option maxHeartbeats 800000

private lemma ae_norm_residual
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
  ∀ᵐ ω ∂(M.traj θ), ∀ j,
    ‖r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)‖ ≤
      (2 / (1 - γ)) * |M.R| := by
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set BV : ℝ := (1 - γ)⁻¹ * |M.R|
  have hBV0 : 0 ≤ BV :=
    mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
  have hrm : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hr_bd : ∀ᵐ ω ∂(M.traj θ), ∀ j, |r j ω| ≤ |M.R| := by
    have hcl : ∀ j,
        r j =ᵐ[M.traj θ] fun ω => clip (ω j).1 (-M.R) M.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M.traj θ), ∀ j,
        r j ω = clip (ω j).1 (-M.R) M.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M.traj θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.R|
    filter_upwards [hr_bd] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M.traj θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BV
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV_ae : ∀ k,
      (fun ω => M.V θ γ k (s k ω)) =ᵐ[M.traj θ]
        Expectation.condSigma (M.traj θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s k)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact hω
  have hVbd : ∀ᵐ ω ∂(M.traj θ), ∀ k, |M.V θ γ k (s k ω)| ≤ BV := by
    have hcond : ∀ k, ∀ᵐ ω ∂(M.traj θ),
        |Expectation.condSigma (M.traj θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BV := fun k => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
          (m := MeasurableSpace.comap (s k) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω k)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm k
    rw [heq k]
    exact hnorm k
  have hB : (2 / (1 - γ)) * |M.R| = |M.R| + (1 + γ) * BV := by
    have hpos : 1 - γ ≠ 0 := (sub_pos.2 h₀.2).ne'
    simp [BV, div_eq_mul_inv, add_mul, mul_assoc]
    field_simp [hpos]
    ring
  filter_upwards [hr_bd, hVbd] with ω hr hv j
  rw [Real.norm_eq_abs]
  have hsum : |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)| ≤
      |r j ω| + |γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| := by
    have h1 := abs_add_le (r j ω) (γ * M.V θ γ (j + 1) (s (j + 1) ω))
    have h2 : |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω)| ≤
        |r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω)) (-M.V θ γ j (s j ω))
    exact h2.trans (add_le_add h1 le_rfl)
  have : |r j ω| + |γ * M.V θ γ (j + 1) (s (j + 1) ω)| + |M.V θ γ j (s j ω)| ≤
      |M.R| + (1 + γ) * BV := by
    have hγV : |γ * M.V θ γ (j + 1) (s (j + 1) ω)| ≤ γ * BV := by
      rw [abs_mul, abs_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hv (j + 1)) h₀.1
    have := add_le_add (add_le_add (hr j) hγV) (hv j)
    have hrew : γ * BV + BV = (1 + γ) * BV := by ring
    simpa [hrew, add_assoc] using this
  exact hsum.trans (this.trans_eq hB.symm)


private lemma integral_delta_smul_eq_zero
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  (t n : ℕ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.π[θ] z.1 z.2))
  (h₂ : t ≤ n)
  (θ : Θ)
  (hVm : ∀ k, Measurable (M.V θ γ k))
  (ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
  ∫ ω, (r (n + 1) ω + γ * M.V θ γ (n + 1 + 1) (s (n + 1 + 1) ω) - M.V θ γ (n + 1) (s (n + 1) ω)) •
    ψ (s t ω) (a t ω) ∂(M.traj θ) = 0 := by
  obtain ⟨Ms, hMs⟩ := hMs
  refine ContinuousLinearMap.ext fun v => ?_
  have hφ : StronglyMeasurable (Function.uncurry fun y u => (ψ y u) v) :=
    (continuous_eval_const v).comp_stronglyMeasurable hψ
  have hφb : ∃ Ms' : ℝ, ∀ y u, ‖(ψ y u) v‖ ≤ Ms' :=
    ⟨Ms * ‖v‖, fun y u =>
      (ContinuousLinearMap.le_opNorm (ψ y u) v).trans
        (mul_le_mul_of_nonneg_right (hMs y u) (norm_nonneg v))⟩
  set Bδ : ℝ := (2 / (1 - γ)) * |M.R|
  have hInt :
      Integrable (fun ω =>
        (r (n + 1) ω + γ * M.V θ γ (n + 1 + 1) (s (n + 1 + 1) ω) - M.V θ γ (n + 1) (s (n + 1) ω)) •
          ψ (s t ω) (a t ω)) (M.traj θ) := by
    refine Integrable.of_bound
      ((((Random.Measurable.of.All_Eq.fst h₁ (n + 1)).add
          ((((hVm (n + 1 + 1))).comp
            (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1 + 1))).const_mul γ)).sub
        (((hVm (n + 1))).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁ (n + 1)))).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (Bδ * Ms) ?_
    filter_upwards [ae_norm_residual (M := M) h₀ h₁ θ] with ω hδ
    rw [norm_smul]
    have hB0 : 0 ≤ Bδ :=
      mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt (sub_pos.2 h₀.2)))
        (abs_nonneg _)
    exact mul_le_mul (hδ _) (hMs _ _) (norm_nonneg _) hB0
  rw [ContinuousLinearMap.integral_apply hInt v]
  simp_rw [smul_apply, smul_eq_mul]
  exact Integral_SMul.eq.Zero.of.Le.In_Ico.All_EqWithDensity
    (M := M) t n h₀ h₁ hπ h₂ θ hVm (fun y u => (ψ y u) v) hφ hφb


/--
GAE reduction under the continuous-action path law:
`∫ ((∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])) = ∫ (δ[t] • ψ(s[t], a[t]))`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ c : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.π[θ] z.1 z.2))
  (θ : Θ)
  (hVm : ∀ k, Measurable (M.V θ γ k))
  (h₂ : c ∈ Set.Ico 0 1)
  (t : ℕ)
  (ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ)
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms) :
-- imply
  ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
    M.V θ γ (t + k) (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M.traj θ) =
    ∫ ω, (r t ω + γ * M.V θ γ (t + 1) (s (t + 1) ω) - M.V θ γ t (s t ω)) •
      ψ (s t ω) (a t ω) ∂(M.traj θ) := by
-- proof
  classical
  obtain ⟨Ms, hMs⟩ := hMs
  let F : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → (Θ →L[ℝ] ℝ) := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
      M.V θ γ (t + k) (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  set Bδ : ℝ := (2 / (1 - γ)) * |M.R|
  have hB0 : 0 ≤ Bδ :=
    mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt (sub_pos.2 h₀.2)))
      (abs_nonneg _)
  have hδm : ∀ k, Measurable fun ω =>
      r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω) := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
      ((((hVm (t + k + 1))).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
      (((hVm (t + k))).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))
  have hFi : ∀ k, Integrable (F k) (M.traj θ) := fun k => by
    refine Integrable.of_bound
      (((hδm k).const_mul (c ^ k)).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (c ^ k * (Bδ * Ms)) ?_
    filter_upwards [ae_norm_residual (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMs _ _) (norm_nonneg _) hB0
  have hFb : ∀ k, ∀ᵐ ω ∂(M.traj θ), ‖F k ω‖ ≤ c ^ k * (Bδ * Ms) := fun k => by
    filter_upwards [ae_norm_residual (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (hMs _ _) (norm_nonneg _) hB0
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M.traj θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right (Bδ * Ms))
    calc
      _ ≤ ∫ _, c ^ k * (Bδ * Ms) ∂(M.traj θ) :=
        integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * (Bδ * Ms) := by simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, k ≠ 0 → ∫ ω, F k ω ∂(M.traj θ) = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := integral_delta_smul_eq_zero (M := M) t (t + k') h₀ h₁ hπ (Nat.le_add_right t k') θ hVm ψ hψ ⟨Ms, hMs⟩
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.V θ γ (t + k'.succ + 1) (s (t + k'.succ + 1) ω) -
        M.V θ γ (t + k'.succ) (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.V θ γ (t + k' + 1 + 1) (s (t + k' + 1 + 1) ω) - M.V θ γ (t + k' + 1) (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M.traj θ) = ∫ ω, F 0 ω ∂(M.traj θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M.traj θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [ae_norm_residual (M := M) h₀ h₁ θ] with ω h
    have hs : Summable (fun k => c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right Bδ)
        fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₂.1]
      exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg h₂.1 k)
    exact (hs.tsum_smul_const _).symm
  rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
  simp [F]


-- created on 2026-10-20
-- updated on 2026-11-17