import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Conditional
import Initialize.Tactic.Attr.Basic
import Syntax.Probability.JointRv.Part6
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {r : Ω → β}
  {a : Ω → γ}
  {s : Ω → δ}
  {G : β → ℝ}
-- given
  (hG : Measurable G)
  (hr : Measurable (r, a, s))
  (h₀ : Integrable (G ∘ r) π)
  (h₁ : r ⟂ᵢ[π] a | s) :
-- imply
  𝔼[r: π](G r | a, s) =ᵐ[π] 𝔼[r: π](G r | s) := by
-- proof
  replace h₀ : Integrable (fun ω ↦ G (r ω)) π := h₀
  have hm_r : Measurable r := hr.fst
  have hm_a : Measurable a := hr.snd.fst
  have hm_s : Measurable s := hr.snd.snd
  show π[(fun ω ↦ G (r ω)) | MeasurableSpace.comap (a, s) inferInstance] =ᵐ[π] π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)]
  have hms : (MeasurableSpace.comap s inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := hm_s.comap_le
  have hJ : Measurable (a, s) := hm_a.prodMk hm_s
  have hmJ : MeasurableSpace.comap (a, s) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hJ.comap_le
  have hsJ : (MeasurableSpace.comap s inferInstance) ≤ MeasurableSpace.comap (a, s) inferInstance :=
    (measurable_snd.comp (comap_measurable (a, s))).comap_le
  have hsC : ∀ C : Set δ, MeasurableSet C → MeasurableSet[(MeasurableSpace.comap s inferInstance)] (s ⁻¹' C) := fun C hC ↦ ⟨C, hC, rfl⟩
  have hprod := (condIndepFun_iff_condExp_inter_preimage_eq_mul hm_r hm_a).1 h₁
  -- `w E = π[1_E | σ(s)]` takes values in `[0, 1]`
  have hind : ∀ {E : Set Ω}, MeasurableSet E → Integrable (E.indicator fun _ ↦ (1 : ℝ)) π :=
    fun hE ↦ (integrable_const 1).indicator hE
  have hind_le : ∀ E : Set Ω, ∀ᵐ ω ∂π, ‖E.indicator (fun _ ↦ (1 : ℝ)) ω‖ ≤ 1 := fun E ↦
    Filter.Eventually.of_forall fun ω ↦ (norm_indicator_le_norm_self (fun _ ↦ (1 : ℝ)) ω).trans_eq norm_one
  have hw_nn : ∀ E : Set Ω, 0 ≤ᵐ[π] π[E.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] := fun E ↦
    condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω)
  have hw_le : ∀ E : Set Ω, ∀ᵐ ω ∂π, ‖π[E.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] ω‖ ≤ 1 := by
    intro E
    have := ae_bdd_abs_condExp_of_ae_bdd_abs (m := (MeasurableSpace.comap s inferInstance)) (μ := π)
      (R := (1 : ℝ)) (f := E.indicator fun _ ↦ (1 : ℝ))
      ((hind_le E).mono fun ω h ↦ by rwa [Real.norm_eq_abs] at h)
    exact this.mono fun ω h ↦ by simpa [Real.norm_eq_abs] using h
  have hw_m : ∀ E : Set Ω, Measurable (π[E.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)]) := fun E ↦
    (stronglyMeasurable_condExp.mono hms).measurable
  -- the law of `r` on `{s ∈ C} ∩ {a ∈ B}` has density `1_{s ∈ C} · π[1_{a ∈ B} | σ(s)]`
  have hstar : ∀ B C, MeasurableSet B → MeasurableSet C →
      ∫ ω in s ⁻¹' C ∩ a ⁻¹' B, G (r ω) ∂π = ∫ ω in s ⁻¹' C, π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] ω * G (r ω) ∂π := by
    intro B C hB hC
    have haB : MeasurableSet (a ⁻¹' B) := hm_a hB
    set w := π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] with hw
    set v : Ω → ℝ := (s ⁻¹' C).indicator w with hv
    have hv_nn : 0 ≤ᵐ[π] v := (hw_nn _).mono fun ω (h : 0 ≤ w ω) ↦ Set.indicator_apply_nonneg fun _ ↦ h
    have hv_int : Integrable v π := integrable_condExp.indicator (hm_s hC)
    have hv_m : Measurable v := (hw_m _).indicator (hm_s hC)
    have hν : (π.restrict (s ⁻¹' C ∩ a ⁻¹' B)).map r = (π.withDensity fun ω ↦ ENNReal.ofReal (v ω)).map r := by
      ext A hA
      have hra : MeasurableSet (r ⁻¹' A) := hm_r hA
      have hint1 : Integrable ((r ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w) π :=
        integrable_condExp.bdd_mul (hind hra).aestronglyMeasurable (hind_le _)
      rw [Measure.map_apply hm_r hA, Measure.map_apply hm_r hA, Measure.restrict_apply hra,
        withDensity_apply _ hra,
        ← ofReal_integral_eq_lintegral_ofReal hv_int.integrableOn (ae_restrict_of_ae hv_nn),
        ← ENNReal.ofReal_toReal (measure_ne_top π _), ← measureReal_def]
      congr 1
      calc
        _ = ∫ ω in s ⁻¹' C, (r ⁻¹' A ∩ a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) ω ∂π := by
          rw [integral_indicator_const _ (hra.inter haB), smul_eq_mul, mul_one,
            measureReal_restrict_apply (hra.inter haB)]
          congr 1
          ext ω
          simp only [Set.mem_inter_iff]
          tauto
        _ = ∫ ω in s ⁻¹' C, π[(r ⁻¹' A ∩ a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] ω ∂π :=
          (setIntegral_condExp hms (hind (hra.inter haB)) (hsC C hC)).symm
        _ = ∫ ω in s ⁻¹' C, π[(r ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] ω * w ω ∂π :=
          setIntegral_congr_ae (hm_s hC) ((hprod A B hA hB).mono fun ω h _ ↦ h)
        _ = ∫ ω in s ⁻¹' C, π[(r ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w | (MeasurableSpace.comap s inferInstance)] ω ∂π :=
          setIntegral_congr_ae (hm_s hC) ((condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp
            hint1 (hind hra)).mono fun ω h _ ↦ h.symm)
        _ = ∫ ω in s ⁻¹' C, ((r ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w) ω ∂π := setIntegral_condExp hms hint1 (hsC C hC)
        _ = ∫ ω in r ⁻¹' A, v ω ∂π := by
          rw [← integral_indicator (hm_s hC), ← integral_indicator hra]
          congr 1
          ext ω
          by_cases h1 : ω ∈ s ⁻¹' C <;> by_cases h2 : ω ∈ r ⁻¹' A <;> simp [v, h1, h2]
    have hd_m : Measurable fun ω ↦ ENNReal.ofReal (v ω) := ENNReal.measurable_ofReal.comp hv_m
    calc
      _ = ∫ b, G b ∂((π.restrict (s ⁻¹' C ∩ a ⁻¹' B)).map r) := (integral_map hm_r.aemeasurable hG.aestronglyMeasurable).symm
      _ = ∫ b, G b ∂((π.withDensity fun ω ↦ ENNReal.ofReal (v ω)).map r) := by
        rw [hν]
      _ = ∫ ω, G (r ω) ∂(π.withDensity fun ω ↦ ENNReal.ofReal (v ω)) := integral_map hm_r.aemeasurable hG.aestronglyMeasurable
      _ = ∫ ω, (ENNReal.ofReal (v ω)).toReal • G (r ω) ∂π :=
        integral_withDensity_eq_integral_toReal_smul hd_m
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _
      _ = ∫ ω, v ω * G (r ω) ∂π := integral_congr_ae (hv_nn.mono fun ω (h : 0 ≤ v ω) ↦ by simp [ENNReal.toReal_ofReal h])
      _ = ∫ ω in s ⁻¹' C, w ω * G (r ω) ∂π := by
        rw [← integral_indicator (hm_s hC)]
        congr 1
        ext ω
        by_cases h1 : ω ∈ s ⁻¹' C <;> simp [v, h1]
  -- rectangles `{a ∈ B} ∩ {s ∈ C}`
  have hrect : ∀ B C, MeasurableSet B → MeasurableSet C →
      ∫ ω in a ⁻¹' B ∩ s ⁻¹' C, G (r ω) ∂π = ∫ ω in a ⁻¹' B ∩ s ⁻¹' C, π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)] ω ∂π := by
    intro B C hB hC
    have haB : MeasurableSet (a ⁻¹' B) := hm_a hB
    rw [Set.inter_comm, hstar B C hB hC]
    have hwf : Integrable (π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] * fun ω ↦ G (r ω)) π :=
      h₀.bdd_mul integrable_condExp.aestronglyMeasurable (hw_le _)
    have hint2 : Integrable ((a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)]) π :=
      integrable_condExp.bdd_mul (hind haB).aestronglyMeasurable (hind_le _)
    calc
      _ = ∫ ω in s ⁻¹' C, π[π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] * (fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)] ω ∂π :=
        (setIntegral_condExp hms hwf (hsC C hC)).symm
      _ = ∫ ω in s ⁻¹' C, (π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap s inferInstance)] * π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)]) ω ∂π :=
        setIntegral_congr_ae (hm_s hC) ((condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
          hwf h₀).mono fun ω h _ ↦ h)
      _ = ∫ ω in s ⁻¹' C, π[(a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)] | (MeasurableSpace.comap s inferInstance)] ω ∂π :=
        setIntegral_congr_ae (hm_s hC) ((condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp
          hint2 (hind haB)).mono fun ω h _ ↦ h.symm)
      _ = ∫ ω in s ⁻¹' C, ((a ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)]) ω ∂π :=
        setIntegral_condExp hms hint2 (hsC C hC)
      _ = ∫ ω in s ⁻¹' C ∩ a ⁻¹' B, π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)] ω ∂π := by
        rw [← setIntegral_indicator haB]
        refine setIntegral_congr_fun (hm_s hC) fun ω _ ↦ ?_
        by_cases h : ω ∈ a ⁻¹' B <;> simp [h]
  -- Dynkin: all of `σ(a, s)`
  have hkey : ∀ D : Set (γ × δ), MeasurableSet D →
      ∫ ω in (a, s) ⁻¹' D, G (r ω) ∂π = ∫ ω in (a, s) ⁻¹' D, π[(fun ω ↦ G (r ω)) | (MeasurableSpace.comap s inferInstance)] ω ∂π := by
    intro D hD
    induction D, hD using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic t ht =>
      obtain ⟨B, hB, C, hC, rfl⟩ := ht
      have : (a, s) ⁻¹' (B ×ˢ C) = a ⁻¹' B ∩ s ⁻¹' C := by
        ext ω
        simp [JointRandomSymbol]
      rw [this]
      apply hrect B C hB hC
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hJ htm) h₀, setIntegral_compl (hJ htm) integrable_condExp,
        ih, integral_condExp hms]
    | iUnion f hd hfm ih =>
      rw [Set.preimage_iUnion,
        integral_iUnion (fun i ↦ hJ (hfm i)) (fun i j hij ↦ (hd hij).preimage _) h₀.integrableOn,
        integral_iUnion (fun i ↦ hJ (hfm i)) (fun i j hij ↦ (hd hij).preimage _) integrable_condExp.integrableOn]
      apply tsum_congr ih
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmJ h₀ (fun _ _ _ ↦ integrable_condExp.integrableOn) ?_
    (stronglyMeasurable_condExp.mono hsJ).aestronglyMeasurable).symm
  rintro _ ⟨D, hD, rfl⟩ _
  apply Eq.symm
  apply hkey D hD


-- created on 2026-10-10
