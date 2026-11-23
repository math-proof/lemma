import Def.Analysis.Calculus.Gradient.Operators
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.MeasurableRkd
import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real Kernel
set_option maxHeartbeats 800000


/--
One-step policy-gradient identity under the continuous path law at time `t`:
`∫ ∇V0 ∂law(s[t]) = ∫ (rkd + γ * ∫ V0) (s[t], a[t]) • ∇log π ∂(M θ) + γ • ∫ ∇V0 ∂law(s[t+1])`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π θ z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₃ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) μ.measure)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.π θ' z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun θ' => Real.log (M.π θ' y u)) θ‖ < ∞)
  (R : ℝ)
  (t : ℕ) :
-- imply
  let Qf : 𝒮 → 𝒜 → ℝ := fun y u =>
    M.rkd R y u + γ * ∫ z, M.V0 R θ γ z ∂(M.trans (y, u))
  ∫ x, fderiv ℝ (fun θ => M.V0 R θ γ x) θ ∂((M θ).map (s t)) =
    ∫ ω, Qf (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.π θ' (s t ω) (a t ω))) θ ∂(M θ) +
      γ • ∫ x, fderiv ℝ (fun θ => M.V0 R θ γ x) θ ∂((M θ).map (s (t + 1))) := by
-- proof
  let g : 𝒮 → 𝒜 → ℝ :=
    fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)
  obtain ⟨Cg, hCg⟩ := id h₃
  have h₅le : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hCg ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.π θ' y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  classical
  intro Qf
  have hgrad : ∀ θ sₜ aₜ, ‖∇[θ] M.π θ sₜ aₜ‖ ≤ g sₜ aₜ :=
    fun θ x u => le_csSup (hBdd x u) ⟨θ, rfl⟩
  have hπbd : ∀ θ sₜ aₜ, ‖fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ‖ ≤ g sₜ aₜ :=
    fun θ x u => by simpa [gradient, LinearIsometryEquiv.norm_map] using hgrad θ x u
  have hsup := h₃
  have hF := fun x =>
    bellmanFderivClosed
      (M := M) (R := R) h₂ h₃ hBdd hIntg h₀ hπ x θ
  obtain ⟨C, hC⟩ :=
    GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ h₃ hBdd hIntg h₀ hπ R
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.V0 R θ γ y) θ‖ ≤ C := fun y => by
    have h := hC ⟨(θ, y), rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hVfd := fun y =>
    HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ h₃ hBdd hIntg h₀ hπ R y θ
  have hgm : StronglyMeasurable (fun y => fderiv ℝ (fun θ => M.V0 R θ γ y) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ R θ' γ)
      (fun y => (hVfd y).differentiableAt)
  have hQb : ∀ x u, ‖Qf x u‖ ≤ |R| + γ * ((1 - γ)⁻¹ * |R|) := fun x u => by
    unfold Qf
    refine (norm_add_le _ _).trans ?_
    refine add_le_add (NormRkd.le.Abs_R (M := M) R x u) ?_
    rw [norm_mul, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left
      ((norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun y =>
          NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ R θ y)).trans_eq (by simp))
      h₀.1
  have hQm : Measurable (fun z : 𝒮 × 𝒜 => Qf z.1 z.2) := by
    unfold Qf
    refine (MeasurableRkd (M := M) R).add (Measurable.const_mul ?_ γ)
    exact (StronglyMeasurable.integral_kernel_prod_right' (κ := M.transK)
      (f := fun z : (𝒮 × 𝒜) × 𝒮 => M.V0 R θ γ z.2)
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ R θ γ).stronglyMeasurable.comp_measurable
        measurable_snd)).measurable
  set BQ : ℝ := |R| + γ * ((1 - γ)⁻¹ * |R|)
  have hφQ : StronglyMeasurable
    (Function.uncurry fun y u => Qf y u •
        fderiv ℝ (fun θ' => Real.log (M.π θ' y u)) θ) :=
    hQm.stronglyMeasurable.smul hφ
  have hφQC : ∀ y u,
      ‖Qf y u • fderiv ℝ (fun θ' => Real.log (M.π θ' y u)) θ‖ ≤ BQ * Ms :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (hQb y u) (hMsle y u) (norm_nonneg _) ((norm_nonneg _).trans (hQb y u))
  have hrew : ∀ y u,
      Qf y u • fderiv ℝ (fun θ => M.π θ y u) θ =
        M.π θ y u • (Qf y u •
          fderiv ℝ (fun θ' => Real.log (M.π θ' y u)) θ) := by
    intro y u
    have e :=
      EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
        (M := M) h₂ θ y u
    rw [← e, smul_smul, smul_smul, mul_comm (Qf y u)]
  have hscore :
    ∫ sₜ, ∫ aₜ, Qf sₜ aₜ • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ
        ∂ReferenceMeasure.measure ∂((M θ).map (s t)) =
      ∫ ω, Qf (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.π θ' (s t ω) (a t ω))) θ ∂(M θ) :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x =>
      integral_congr_ae (Filter.Eventually.of_forall fun u => hrew x u))).trans
      (Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) h₁ hφQ hφQC θ t).symm
  have hφV : StronglyMeasurable
    (Function.uncurry fun (sₜ : 𝒮) (aₜ : 𝒜) =>
        ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))) :=
    (StronglyMeasurable.integral_kernel_prod_right'
      (κ := M.transK)
      (f := fun z : (𝒮 × 𝒜) × 𝒮 => fderiv ℝ (fun θ => M.V0 R θ γ z.2) θ)
      (hgm.comp_measurable measurable_snd)).measurable.stronglyMeasurable
  have hCV : ∀ x u,
      ‖∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (x, u))‖ ≤ C :=
    fun x u => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := M.trans (x, u)) (Filter.Eventually.of_forall hCb)
  have hnext :
    ∫ sₜ, ∫ aₜ, M.π θ sₜ aₜ •
          ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))
          ∂ReferenceMeasure.measure ∂((M θ).map (s t)) =
        ∫ x, fderiv ℝ (fun θ => M.V0 R θ γ x) θ ∂((M θ).map (s (t + 1))) := by
    have hdecomp :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M)
        (φ := fun x u => ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (x, u)))
        (C := C) h₁ hφV hCV θ t
    have hsa : Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω) :=
      (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
        (Random.Measurable.of.All_Eq.snd.snd h₁ t)
    have hpath :
      ∫ ω, ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ
            ∂(M.trans (s t ω, a t ω)) ∂(M θ) =
          ∫ p : 𝒮 × 𝒜, ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (p.1, p.2))
            ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) :=
      by
        simpa [Function.uncurry] using
          (integral_map (μ := M θ) hsa.aemeasurable
            (f := Function.uncurry fun (sₜ : 𝒮) (aₜ : 𝒜) =>
              ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ)))
            hφV.aestronglyMeasurable).symm
    have hlaw := Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ t
    have hInt : Integrable (fun y => fderiv ℝ (fun θ => M.V0 R θ γ y) θ)
        (M.transK ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω))) := by
      rw [← hlaw]
      exact Integrable.of_bound hgm.aestronglyMeasurable C
        (Filter.Eventually.of_forall hCb)
    calc
      _ = ∫ ω, ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ
            ∂(M.trans (s t ω, a t ω)) ∂(M θ) := hdecomp.symm
      _ = ∫ p : 𝒮 × 𝒜, ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (p.1, p.2))
            ∂((M θ).map (fun ω ↦ (s t ω, a t ω))) := hpath
      _ = ∫ x, fderiv ℝ (fun θ => M.V0 R θ γ x) θ
            ∂(M.transK ∘ₘ (M θ).map (fun ω ↦ (s t ω, a t ω))) :=
        (Integral.eq.Integral_Integral.of.Integrable_Bind hInt).symm
      _ = _ := by rw [hlaw]
  have hI₁ : Integrable
    (fun sₜ => ∫ aₜ, Qf sₜ aₜ • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ
        ∂ReferenceMeasure.measure) ((M θ).map (s t)) := by
    have hsm : StronglyMeasurable
      (Function.uncurry fun y u =>
          Qf y u • fderiv ℝ (fun θ => M.π θ y u) θ) :=
      hQm.stronglyMeasurable.smul
        (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
          (fun θ' => hπ θ') (fun z => (h₂ z.1 z.2).differentiableAt))
    refine Integrable.of_bound hsm.integral_prod_right'.aestronglyMeasurable (BQ * Cg) ?_
    filter_upwards with sₜ
    have hbd : ∀ aₜ, ‖Qf sₜ aₜ • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ‖ ≤
        BQ * g sₜ aₜ := fun u => by
      rw [norm_smul]
      exact mul_le_mul (hQb sₜ u) (hπbd θ sₜ u) (norm_nonneg _)
        ((norm_nonneg _).trans (hQb sₜ u))
    have hnonneg : 0 ≤ BQ :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg h₀.1 (mul_nonneg (inv_nonneg.2 (sub_nonneg.2 h₀.2.le)) (abs_nonneg _)))
    calc
      _ ≤ ∫ u, BQ * g sₜ u ∂ReferenceMeasure.measure :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hIntg sₜ).const_mul BQ) (Filter.Eventually.of_forall hbd))
      _ = BQ * ∫ u, g sₜ u ∂ReferenceMeasure.measure := integral_const_mul _ _
      _ ≤ BQ * Cg := mul_le_mul_of_nonneg_left (h₅le sₜ) hnonneg
  have hI₂ : Integrable
    (fun sₜ => ∫ aₜ, M.π θ sₜ aₜ •
        ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))
        ∂ReferenceMeasure.measure) ((M θ).map (s t)) := by
    have hsm₂ : StronglyMeasurable
      (Function.uncurry fun sₜ aₜ =>
          M.π θ sₜ aₜ •
            ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))) :=
      ((hπ θ).stronglyMeasurable).smul hφV
    refine Integrable.of_bound hsm₂.integral_prod_right'.aestronglyMeasurable C ?_
    filter_upwards with sₜ
    have hbd : ∀ aₜ, ‖M.π θ sₜ aₜ •
        ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))‖ ≤
        M.π θ sₜ aₜ * C := fun u => by
      rw [norm_smul]; erw [Real.norm_of_nonneg (hStoch.nonneg θ sₜ u)]
      exact mul_le_mul_of_nonneg_left (hCV sₜ u) (hStoch.nonneg θ sₜ u)
    calc
      _ ≤ ∫ aₜ, M.π θ sₜ aₜ * C ∂ReferenceMeasure.measure :=
        (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((Integrable.of_integral_ne_zero
              (by erw [hStoch.integral_eq_one θ sₜ]; exact one_ne_zero)).mul_const C)
            (Filter.Eventually.of_forall hbd))
      _ = (∫ aₜ, M.π θ sₜ aₜ ∂ReferenceMeasure.measure) * C := by
        rw [← integral_mul_const]
      _ = C := by erw [hStoch.integral_eq_one θ sₜ]; rw [one_mul]
  have hL :
    ∫ x, fderiv ℝ (fun θ => M.V0 R θ γ x) θ ∂((M θ).map (s t)) =
        ∫ sₜ, ∫ aₜ, Qf sₜ aₜ • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ
            ∂ReferenceMeasure.measure ∂((M θ).map (s t)) +
          γ • ∫ sₜ, ∫ aₜ, M.π θ sₜ aₜ •
            ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))
            ∂ReferenceMeasure.measure ∂((M θ).map (s t)) := by
    have hpt : ∀ sₜ,
        fderiv ℝ (fun θ => M.V0 R θ γ sₜ) θ =
          (∫ aₜ, Qf sₜ aₜ • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ
            ∂ReferenceMeasure.measure) +
          (γ • ∫ aₜ, M.π θ sₜ aₜ •
            ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))
            ∂ReferenceMeasure.measure) :=
      fun x => hF x
    refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
    refine (integral_add hI₁ (hI₂.smul γ)).trans ?_
    exact congrArg _ (integral_smul (c := γ)
      (f := fun sₜ => ∫ aₜ, M.π θ sₜ aₜ •
        ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))
        ∂ReferenceMeasure.measure)
      (μ := (M θ).map (s t)))
  rw [hL, hscore, hnext]


-- created on 2026-10-20
-- updated on 2026-11-18