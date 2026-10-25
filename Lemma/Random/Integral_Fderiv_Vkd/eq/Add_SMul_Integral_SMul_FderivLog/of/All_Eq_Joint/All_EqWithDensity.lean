import Macro.Order.Sup
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Qkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real Kernel
set_option maxHeartbeats 800000


/--
One-step policy-gradient identity under the continuous path law at time `t`:
`∫ ∇Vkd ∂law(s[t]) = ∫ Qkd(s[t], a[t]) • ∇log π ∂(M θ) + γ • ∫ ∇Vkd ∂law(s[t+1])`.
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
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms)
  (t : ℕ) :
-- imply
  ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s t)) =
    ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
      γ • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (t + 1))) := by
-- proof
  classical
  have := M.env.init_prob
  have := M.env.trans_markov
  have hgrad : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u :=
    fun θ x u => by simpa [gradient, LinearIsometryEquiv.norm_map] using h₃ θ x u
  have hsup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞ :=
    ⟨Cg, by rintro _ ⟨x, rfl⟩; exact h₅ x⟩
  have hF := fun x =>
    Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ hgrad h₄ hsup h₀ hπ x θ
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
  have hQb : ∀ x u, ‖M.Qkd θ γ x u‖ ≤ |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) := fun x u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
      (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y)
    unfold DensityModel.Qkd
    refine (norm_add_le _ _).trans (add_le_add (NormRkd.le.Abs_R (M := M) x u) ?_)
    rw [norm_mul, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₀.1
  set BQ : ℝ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)
  have hφQ : StronglyMeasurable
    (Function.uncurry fun y u => M.Qkd θ γ y u •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) :=
    ((Measurable_Qkd.of.All_Measurable_Prob (M := M) hπ θ γ).stronglyMeasurable).smul hφ
  have hφQC : ∀ y u,
      ‖M.Qkd θ γ y u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ BQ * Ms :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (hQb y u) (hMs y u) (norm_nonneg _) ((norm_nonneg _).trans (hQb y u))
  have hrew : ∀ y u,
      M.Qkd θ γ y u • fderiv ℝ (fun θ => M.policy.prob θ y u) θ =
        M.policy.prob θ y u • (M.Qkd θ γ y u •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) := by
    intro y u
    have e :=
      EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
        (M := M) h₂ θ y u
    rw [← e, smul_smul, smul_smul, mul_comm (M.Qkd θ γ y u)]
  have hscore :
    ∫ x, ∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ
        ∂ReferenceMeasure.measure ∂((M θ).map (s t)) =
      ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x =>
      integral_congr_ae (Filter.Eventually.of_forall fun u => hrew x u))).trans
      (Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) h₁ hφQ hφQC θ t).symm
  have hφV : StronglyMeasurable
    (Function.uncurry fun (x : S) (u : A) =>
        ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))) :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (κ := M.env.trans)
      (f := fun z : (S × A) × S => fderiv ℝ (fun θ => M.Vkd θ γ z.2) θ)
      (hgm.comp_measurable measurable_snd)).measurable.stronglyMeasurable
  have hCV : ∀ x u,
      ‖∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))‖ ≤ C :=
    fun x u => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := M.env.trans (x, u)) (Filter.Eventually.of_forall hCb)
  have hnext :
    ∫ x, ∫ u, M.policy.prob θ x u •
          ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))
          ∂ReferenceMeasure.measure ∂((M θ).map (s t)) =
        ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (t + 1))) := by
    have hdecomp :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M)
        (φ := fun x u => ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)))
        (C := C) h₁ hφV hCV θ t
    have hsa : Measurable fun ω : ℕ → ℝ × S × A => (s t ω, a t ω) :=
      (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
        (Random.Measurable.of.All_Eq.snd.snd h₁ t)
    have hpath :
      ∫ ω, ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ
            ∂(M.env.trans (s t ω, a t ω)) ∂(M θ) =
          ∫ p : S × A, ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans p)
            ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) :=
      (integral_map (μ := M θ) hsa.aemeasurable
        (f := fun p : S × A =>
          ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans p))
        hφV.aestronglyMeasurable).symm
    have hlaw := Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ t
    have hInt : Integrable (fun y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ)
        (M.env.trans ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω))) := by
      rw [← hlaw]
      exact Integrable.of_bound hgm.aestronglyMeasurable C
        (Filter.Eventually.of_forall hCb)
    calc
      _ = ∫ ω, ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ
            ∂(M.env.trans (s t ω, a t ω)) ∂(M θ) := hdecomp.symm
      _ = ∫ p : S × A, ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans p)
            ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) := hpath
      _ = ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ
            ∂(M.env.trans ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω))) :=
        (Integral.eq.Integral_Integral.of.Integrable_Bind hInt).symm
      _ = _ := by rw [hlaw]
  have hI₁ : Integrable
    (fun x => ∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ
        ∂ReferenceMeasure.measure) ((M θ).map (s t)) := by
    have hsm : StronglyMeasurable
      (Function.uncurry fun y u =>
          M.Qkd θ γ y u • fderiv ℝ (fun θ => M.policy.prob θ y u) θ) :=
      ((Measurable_Qkd.of.All_Measurable_Prob (M := M) hπ θ γ).stronglyMeasurable).smul
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' => hπ θ') (fun z => (h₂ z.1 z.2).differentiableAt))
    refine Integrable.of_bound hsm.integral_prod_right'.aestronglyMeasurable (BQ * Cg) ?_
    filter_upwards with x
    have hbd : ∀ u, ‖M.Qkd θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤
        BQ * g x u := fun u => by
      rw [norm_smul]
      exact mul_le_mul (hQb x u) (h₃ θ x u) (norm_nonneg _)
        ((norm_nonneg _).trans (hQb x u))
    have hnonneg : 0 ≤ BQ :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg h₀.1 (mul_nonneg (inv_nonneg.2 (sub_nonneg.2 h₀.2.le)) (abs_nonneg _)))
    calc
      _ ≤ ∫ u, BQ * g x u ∂ReferenceMeasure.measure :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((h₄ x).const_mul BQ) (Filter.Eventually.of_forall hbd))
      _ = BQ * ∫ u, g x u ∂ReferenceMeasure.measure := integral_const_mul _ _
      _ ≤ BQ * Cg := mul_le_mul_of_nonneg_left (h₅ x) hnonneg
  have hI₂ : Integrable
    (fun x => ∫ u, M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))
        ∂ReferenceMeasure.measure) ((M θ).map (s t)) := by
    have hsm₂ : StronglyMeasurable
      (Function.uncurry fun x u =>
          M.policy.prob θ x u •
            ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))) :=
      ((hπ θ).stronglyMeasurable).smul hφV
    refine Integrable.of_bound hsm₂.integral_prod_right'.aestronglyMeasurable C ?_
    filter_upwards with x
    have hbd : ∀ u, ‖M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))‖ ≤
        M.policy.prob θ x u * C := fun u => by
      rw [norm_smul, Real.norm_of_nonneg (M.policy.nonneg θ x u)]
      exact mul_le_mul_of_nonneg_left (hCV x u) (M.policy.nonneg θ x u)
    calc
      _ ≤ ∫ u, M.policy.prob θ x u * C ∂ReferenceMeasure.measure :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((Integrable.of_integral_ne_zero
              (by simp [M.policy.integral_eq_one θ x])).mul_const C)
            (Filter.Eventually.of_forall hbd))
      _ = (∫ u, M.policy.prob θ x u ∂ReferenceMeasure.measure) * C := by
        rw [← integral_mul_const]
      _ = C := by rw [M.policy.integral_eq_one, one_mul]
  have hL :
    ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s t)) =
        ∫ x, ∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ
            ∂ReferenceMeasure.measure ∂((M θ).map (s t)) +
          γ • ∫ x, ∫ u, M.policy.prob θ x u •
            ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))
            ∂ReferenceMeasure.measure ∂((M θ).map (s t)) := by
    have hpt : ∀ x,
        fderiv ℝ (fun θ => M.Vkd θ γ x) θ =
          (∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.policy.prob θ x u) θ
            ∂ReferenceMeasure.measure) +
          (γ • ∫ u, M.policy.prob θ x u •
            ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))
            ∂ReferenceMeasure.measure) :=
      fun x => hF x
    refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
    refine (integral_add hI₁ (hI₂.smul γ)).trans ?_
    exact congrArg _ (integral_smul (c := γ)
      (f := fun x => ∫ u, M.policy.prob θ x u •
        ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u))
        ∂ReferenceMeasure.measure)
      (μ := (M θ).map (s t)))
  rw [hL, hscore, hnext]


-- created on 2026-10-20
