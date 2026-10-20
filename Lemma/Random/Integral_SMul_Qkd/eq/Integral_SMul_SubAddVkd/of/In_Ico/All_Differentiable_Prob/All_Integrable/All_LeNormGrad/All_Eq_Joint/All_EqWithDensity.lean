import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.CompProd.of.All_EqWithDensity
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Qkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.MeasurableRkd
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Real Kernel
set_option maxHeartbeats 800000


private lemma integral_rkd_smul
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} {θ : Θ} {Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {ψ : S → A → Θ →L[ℝ] ℝ}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∀ y u, ‖ψ y u‖ ≤ Ms)
  (t : ℕ) :
  ∫ ω, r t ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, M.rkd (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
  have := M.env.reward_markov
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₁' : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => by
    simp only [r, s, a, JointRandomSymbol]
  have hclip := MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁' θ t
  have hf : StronglyMeasurable fun z : ℝ × S × A =>
      clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2 :=
    (((measurable_fst.max measurable_const).min measurable_const).stronglyMeasurable).smul
      (hψ.comp_measurable (measurable_snd.fst.prodMk measurable_snd.snd))
  have hCb : ∀ z : ℝ × S × A,
      ‖clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2‖ ≤ |M.env.R| * Ms :=
    fun z => by
      rw [norm_smul]
      exact mul_le_mul (NormClip.le.Abs_R M.env.R z.1) (hMs _ _) (norm_nonneg _)
        ((norm_nonneg _).trans (NormClip.le.Abs_R M.env.R z.1))
  have hmap := Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁' θ t
  have hInt : Integrable (fun z : ℝ × S × A =>
      clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2)
      (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall hCb)
  have hL :
      ∫ ω, r t ω • ψ (s t ω) (a t ω) ∂(M θ) =
        ∫ y, ∫ z, clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2 ∂(M.stageK θ y)
          ∂((M θ).map (s t)) := by
    have e₁ := integral_congr_ae <| hclip.mono fun ω h =>
      congrArg (· • ψ (s t ω) (a t ω)) h
    have e₂ := integral_map (μ := M θ) (measurable_pi_apply t).aemeasurable
      (f := fun z : ℝ × S × A => clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2)
      hf.aestronglyMeasurable
    exact e₁.trans (e₂.symm.trans (by rw [hmap, Integral.eq.Integral_Integral.of.Integrable_Bind hInt]))
  have hinner : ∀ y,
      ∫ z, clip z.1 (-M.env.R) M.env.R • ψ z.2.1 z.2.2 ∂(M.stageK θ y) =
        ∫ u, M.policy.prob θ y u • (M.rkd y u • ψ y u) ∂ReferenceMeasure.measure := by
    intro y
    have e :=
      Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
        (M := M) hf hCb θ y
    refine e.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    -- stage integrand at (ρ, y, u) is clip ρ • ψ y u
    change M.policy.prob θ y u •
        ∫ ρ, clip ρ (-M.env.R) M.env.R • ψ y u ∂(M.env.reward (y, u)) =
      M.policy.prob θ y u • (M.rkd y u • ψ y u)
    have hr :
        ∫ ρ, clip ρ (-M.env.R) M.env.R • ψ y u ∂(M.env.reward (y, u)) =
          (∫ ρ, clip ρ (-M.env.R) M.env.R ∂(M.env.reward (y, u))) • ψ y u :=
      integral_smul_const _ _
    rw [hr]
    rfl
  have hφrkd : StronglyMeasurable
      (Function.uncurry fun y u => M.rkd y u • ψ y u) :=
    ((MeasurableRkd (M := M)).stronglyMeasurable).smul hψ
  have hCrkd : ∀ y u, ‖M.rkd y u • ψ y u‖ ≤ |M.env.R| * Ms :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (NormRkd.le.Abs_R (M := M) y u) (hMs y u) (norm_nonneg _)
        ((norm_nonneg _).trans (NormRkd.le.Abs_R (M := M) y u))
  refine hL.trans ?_
  simp_rw [hinner]
  exact (Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
    (M := M) h₁' hφrkd hCrkd θ t).symm



private lemma integral_Vkd_succ_smul
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A} {θ : Θ} {γ : ℝ} {Ms BV : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {ψ : S → A → Θ →L[ℝ] ℝ}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∀ y u, ‖ψ y u‖ ≤ Ms)
  (hBV : ∀ x, ‖M.Vkd θ γ x‖ ≤ BV)
  (t : ℕ) :
  ∫ ω, M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (∫ y, M.Vkd θ γ y ∂(M.env.trans (s t ω, a t ω))) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
  have := M.env.trans_markov
  have := M.env.reward_markov
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hmeasV : Measurable (M.Vkd θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ
  have hf : StronglyMeasurable fun p : (ℝ × S × A) × (ℝ × S × A) =>
      M.Vkd θ γ p.2.2.1 • ψ p.1.2.1 p.1.2.2 :=
    (hmeasV.comp (measurable_snd.snd.fst)).stronglyMeasurable.smul
      (hψ.comp_measurable (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd))
  have hCb : ∀ p : (ℝ × S × A) × (ℝ × S × A),
      ‖M.Vkd θ γ p.2.2.1 • ψ p.1.2.1 p.1.2.2‖ ≤ BV * Ms := by
    intro p
    rw [norm_smul]
    exact mul_le_mul (hBV p.2.2.1) (hMs _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hBV p.2.2.1))
  have hcomp := Map.eq.CompProd.of.All_EqWithDensity (M := M) θ t
  have hInt : Integrable (fun p : (ℝ × S × A) × (ℝ × S × A) =>
      M.Vkd θ γ p.2.2.1 • ψ p.1.2.1 p.1.2.2)
      (((M θ).map (fun ω => ω t)) ⊗ₘ M.K θ) :=
    Integrable.of_bound hf.aestronglyMeasurable _ (Filter.Eventually.of_forall hCb)
  have hL :
      ∫ ω, M.Vkd θ γ ((ω (t + 1)).2.1) • ψ (ω t).2.1 (ω t).2.2 ∂(M θ) =
        ∫ z, (∫ w, M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2 ∂(M.K θ z))
          ∂((M θ).map (fun ω => ω t)) := by
    have e := integral_map (μ := M θ)
      ((measurable_pi_apply t).prodMk (measurable_pi_apply (t + 1))).aemeasurable
      (f := fun p : (ℝ × S × A) × (ℝ × S × A) =>
        M.Vkd θ γ p.2.2.1 • ψ p.1.2.1 p.1.2.2) hf.aestronglyMeasurable
    exact e.symm.trans (by
      rw [hcomp]
      exact ProbabilityTheory.integral_compProd hInt)
  -- s/a are projections
  change ∫ ω, M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω) ∂(M θ) = _
  refine hL.trans ?_
  have hKinner : ∀ z : ℝ × S × A,
      ∫ w, M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2 ∂(M.K θ z) =
        (∫ y, M.Vkd θ γ y ∂(M.env.trans z.2)) • ψ z.2.1 z.2.2 := by
    intro z
    have hKz : M.K θ z = M.stageK θ ∘ₘ (M.env.trans z.2) := by
      unfold DensityModel.K
      rw [Kernel.comp_apply, Kernel.comap_apply]
    simp_rw [hKz]
    have hbind : Integrable (fun w : ℝ × S × A => M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2)
        (M.stageK θ ∘ₘ (M.env.trans z.2)) :=
      Integrable.of_bound
        ((hmeasV.comp measurable_snd.fst).stronglyMeasurable.smul
          stronglyMeasurable_const).aestronglyMeasurable (BV * Ms)
        (Filter.Eventually.of_forall fun w => by
          rw [norm_smul]
          exact mul_le_mul (hBV w.2.1) (hMs z.2.1 z.2.2) (norm_nonneg _)
            ((norm_nonneg _).trans (hBV w.2.1)))
    rw [Integral.eq.Integral_Integral.of.Integrable_Bind hbind]
    have hstage : ∀ y,
        ∫ w, M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2 ∂(M.stageK θ y) =
          M.Vkd θ γ y • ψ z.2.1 z.2.2 := by
      intro y
      have hf' : StronglyMeasurable fun w : ℝ × S × A =>
          M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2 :=
        (hmeasV.comp measurable_snd.fst).stronglyMeasurable.smul stronglyMeasurable_const
      have hC' : ∀ w : ℝ × S × A, ‖M.Vkd θ γ w.2.1 • ψ z.2.1 z.2.2‖ ≤ BV * Ms :=
        fun w => by
          rw [norm_smul]
          exact mul_le_mul (hBV w.2.1) (hMs z.2.1 z.2.2) (norm_nonneg _)
            ((norm_nonneg _).trans (hBV w.2.1))
      have e :=
        Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
          (M := M) hf' hC' θ y
      refine e.trans ?_
      have hconst : ∀ u,
          ∫ ρ, M.Vkd θ γ y • ψ z.2.1 z.2.2 ∂(M.env.reward (y, u)) =
            M.Vkd θ γ y • ψ z.2.1 z.2.2 := fun u => by
        have := M.env.reward_markov
        have : IsProbabilityMeasure (M.env.reward (y, u)) := inferInstance
        rw [MeasureTheory.integral_const, probReal_univ, one_smul]
      simp_rw [hconst]
      rw [integral_smul_const, M.policy.integral_eq_one θ y, one_smul]
    simp_rw [hstage]
    exact integral_smul_const (M.Vkd θ γ) (ψ z.2.1 z.2.2)
  simp_rw [hKinner]
  have hTsm : StronglyMeasurable fun p : S × A =>
      (∫ y, M.Vkd θ γ y ∂(M.env.trans p)) • ψ p.1 p.2 :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (κ := M.env.trans) (f := fun z : (S × A) × S => M.Vkd θ γ z.2)
      (hmeasV.comp measurable_snd).stronglyMeasurable).smul hψ
  have e := integral_map (μ := (M θ).map (fun ω => ω t))
    (measurable_snd.fst.prodMk measurable_snd.snd).aemeasurable
    (f := fun p : S × A => (∫ y, M.Vkd θ γ y ∂(M.env.trans p)) • ψ p.1 p.2)
    hTsm.aestronglyMeasurable
  refine e.symm.trans ?_
  rw [Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd) (measurable_pi_apply t)]
  exact (integral_map (μ := M θ)
    ((measurable_snd.fst.comp (measurable_pi_apply t)).prodMk
      (measurable_snd.snd.comp (measurable_pi_apply t))).aemeasurable
    (f := fun p : S × A => (∫ y, M.Vkd θ γ y ∂(M.env.trans p)) • ψ p.1 p.2)
    hTsm.aestronglyMeasurable)


/--
`∫ Qkd(s[t], a[t]) • ∇log π = ∫ (r[t] + γ • Vkd(s[t+1]) - Vkd(s[t])) • ∇log π`.
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
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms)
  (t : ℕ) :
-- imply
  ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
    ∫ ω, (r t ω + γ * M.Vkd θ γ (s (t + 1) ω) - M.Vkd θ γ (s t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  classical
  set ψ : S → A → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ
  have hBV : ∀ x, ‖M.Vkd θ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    fun x => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ x
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hmeasV : Measurable (M.Vkd θ γ) :=
    Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ
  have hV0 :
      ∫ ω, M.Vkd θ γ (s t ω) • ψ (s t ω) (a t ω) ∂(M θ) = 0 :=
    Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
      (M := M) (θ := θ) h₁ h₂ h₃ h₄ (M.Vkd θ γ) hmeasV
      (fun y => by simpa [Real.norm_eq_abs] using hBV y) hφ hMs t
  have hrkd := integral_rkd_smul (M := M) (θ := θ) (Ms := Ms) h₁ hψ hMs t
  have hVsucc := integral_Vkd_succ_smul (M := M) (θ := θ) (γ := γ) (Ms := Ms) (BV := BV)
    h₁ hπ hψ hMs hBV t
  have hIntR : Integrable (fun ω => r t ω • ψ (s t ω) (a t ω)) (M θ) := by
    refine Integrable.of_bound
      (((Random.Measurable.of.All_Eq.fst h₁ t).stronglyMeasurable).smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (|M.env.R| * Ms) ?_
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hr
    rw [norm_smul]
    exact mul_le_mul (hr t) (hMs (s t ω) (a t ω)) (norm_nonneg _)
      ((norm_nonneg _).trans (hr t))
  have hIntVsucc : Integrable (fun ω =>
      M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      ((hmeasV.comp (Random.Measurable.of.All_Eq.snd.fst h₁ (t + 1))).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (BV * Ms) (Filter.Eventually.of_forall fun ω => by
        rw [norm_smul]
        exact mul_le_mul (hBV (s (t + 1) ω)) (hMs (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans (hBV (s (t + 1) ω))))
  have hIntV : Integrable (fun ω => M.Vkd θ γ (s t ω) • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      ((hmeasV.comp (Random.Measurable.of.All_Eq.snd.fst h₁ t)).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (BV * Ms) (Filter.Eventually.of_forall fun ω => by
        rw [norm_smul]
        exact mul_le_mul (hBV (s t ω)) (hMs (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans (hBV (s t ω))))
  have hIntRkd : Integrable (fun ω => M.rkd (s t ω) (a t ω) • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      (((MeasurableRkd (M := M)).comp
        ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
          (Random.Measurable.of.All_Eq.snd.snd h₁ t))).stronglyMeasurable.smul
        (hψ.comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).aestronglyMeasurable
      (|M.env.R| * Ms) (Filter.Eventually.of_forall fun ω => by
        rw [norm_smul]
        exact mul_le_mul (NormRkd.le.Abs_R (M := M) (s t ω) (a t ω))
          (hMs (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans (NormRkd.le.Abs_R (M := M) (s t ω) (a t ω))))
  have := M.env.trans_markov
  have hIntT : Integrable (fun ω =>
      (∫ y, M.Vkd θ γ y ∂(M.env.trans (s t ω, a t ω))) • ψ (s t ω) (a t ω)) (M θ) :=
    Integrable.of_bound
      (((StronglyMeasurable.integral_kernel_prod_right'
          (κ := M.env.trans) (f := fun z : (S × A) × S => M.Vkd θ γ z.2)
          (hmeasV.comp measurable_snd).stronglyMeasurable).smul hψ).comp_measurable
        ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
          (Random.Measurable.of.All_Eq.snd.snd h₁ t))).aestronglyMeasurable
      (BV * Ms) (Filter.Eventually.of_forall fun ω => by
        let μ := M.env.trans (s t ω, a t ω)
        have : IsProbabilityMeasure μ := inferInstance
        have hbound : ‖∫ y, M.Vkd θ γ y ∂μ‖ ≤ BV := by
          refine (norm_integral_le_of_norm_le_const
            (Filter.Eventually.of_forall fun y => hBV y)).trans ?_
          rw [probReal_univ (μ := μ), mul_one]
        rw [norm_smul]
        exact mul_le_mul hbound (hMs (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans hbound))
  have hL :
      ∫ ω, M.Qkd θ γ (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) =
        ∫ ω, M.rkd (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) +
          γ • ∫ ω, (∫ y, M.Vkd θ γ y ∂(M.env.trans (s t ω, a t ω))) •
            ψ (s t ω) (a t ω) ∂(M θ) := by
    have hpt :
        (fun ω => M.Qkd θ γ (s t ω) (a t ω) • ψ (s t ω) (a t ω)) =
          (fun ω => M.rkd (s t ω) (a t ω) • ψ (s t ω) (a t ω)) +
            γ • (fun ω => (∫ y, M.Vkd θ γ y ∂(M.env.trans (s t ω, a t ω))) •
              ψ (s t ω) (a t ω)) := by
      funext ω
      dsimp only [Pi.add_apply, Pi.smul_apply]
      rw [DensityModel.Qkd, add_smul, ← mul_smul]
    rw [hpt]
    refine (integral_add hIntRkd (hIntT.smul γ)).trans ?_
    simp only [Pi.smul_apply, integral_smul]
  calc
    _ = ∫ ω, M.rkd (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) +
          γ • ∫ ω, (∫ y, M.Vkd θ γ y ∂(M.env.trans (s t ω, a t ω))) •
            ψ (s t ω) (a t ω) ∂(M θ) := hL
    _ = ∫ ω, r t ω • ψ (s t ω) (a t ω) ∂(M θ) +
          γ • ∫ ω, M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
      rw [← hrkd, ← hVsucc]
    _ = ∫ ω, r t ω • ψ (s t ω) (a t ω) ∂(M θ) +
          γ • ∫ ω, M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω) ∂(M θ) -
          ∫ ω, M.Vkd θ γ (s t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
      rw [hV0, sub_zero]
    _ = ∫ ω, (r t ω + γ * M.Vkd θ γ (s (t + 1) ω) - M.Vkd θ γ (s t ω)) •
          ψ (s t ω) (a t ω) ∂(M θ) := by
      have hpt :
          (fun ω =>
            (r t ω + γ * M.Vkd θ γ (s (t + 1) ω) - M.Vkd θ γ (s t ω)) •
              ψ (s t ω) (a t ω)) =
            (fun ω => r t ω • ψ (s t ω) (a t ω)) +
              γ • (fun ω => M.Vkd θ γ (s (t + 1) ω) • ψ (s t ω) (a t ω)) -
              fun ω => M.Vkd θ γ (s t ω) • ψ (s t ω) (a t ω) := by
        funext ω
        dsimp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
        -- goal: (rt+γV-V')•ψ = rt•ψ + γ•(V•ψ) - V'•ψ
        refine (sub_smul (r t ω + γ * M.Vkd θ γ (s (t + 1) ω))
            (M.Vkd θ γ (s t ω)) (ψ (s t ω) (a t ω))).trans ?_
        refine congrArg₂ (· - ·) ?_ rfl
        refine (add_smul (r t ω) (γ * M.Vkd θ γ (s (t + 1) ω))
            (ψ (s t ω) (a t ω))).trans ?_
        refine congrArg₂ (· + ·) rfl ?_
        exact mul_smul γ (M.Vkd θ γ (s (t + 1) ω)) (ψ (s t ω) (a t ω))

      refine Eq.symm ?_
      rw [hpt]
      refine (integral_sub (hIntR.add (hIntVsucc.smul γ)) hIntV).trans ?_
      refine congrArg (· - ∫ ω, M.Vkd θ γ (s t ω) • ψ (s t ω) (a t ω) ∂(M θ)) ?_
      refine (integral_add hIntR (hIntVsucc.smul γ)).trans ?_
      simp only [Pi.smul_apply, integral_smul]

-- created on 2026-10-20
