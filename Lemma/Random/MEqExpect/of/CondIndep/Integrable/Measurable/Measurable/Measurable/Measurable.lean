import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Independence.Conditional
import sympy.Basic
import sympy.stats.joint_rv
open MeasureTheory ProbabilityTheory


/--
Conditional independence `F ⟂ᵢ[π] X | Z` lets one drop `X` from the conditioning:
`𝔼[g(F) | X, Z] = 𝔼[g(F) | Z]` π-a.e., for every measurable `g` with `g ∘ F` integrable
(σ-algebra conditional expectations, `Expectation.condSigma`; `X, Z` packs `JointRandomSymbol X Z`).
Proof: for rectangles `{X ∈ B} ∩ {Z ∈ C}` the product formula
`condIndepFun_iff_condExp_inter_preimage_eq_mul` gives, for every `A`, the identity of the laws of `F` under
`π.restrict ({Z ∈ C} ∩ {X ∈ B})` and under `π.withDensity (1_{Z ∈ C} · π[1_{X ∈ B} | σ(Z)])`, hence
`∫_{X ∈ B, Z ∈ C} g(F) = ∫_{Z ∈ C} π[1_{X ∈ B} | σ(Z)] · g(F) = ∫_{X ∈ B, Z ∈ C} π[g(F) | σ(Z)]`;
Dynkin's π-λ theorem extends this to `σ(X, Z)` and `ae_eq_condExp_of_forall_setIntegral_eq` concludes.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {π : Measure Ω} [IsFiniteMeasure π]
  {F : Ω → β}
  {X : Ω → γ}
  {Z : Ω → δ}
  {g : β → ℝ}
-- given
  (h₀ : Measurable F)
  (h₁ : Measurable X)
  (h₂ : Measurable Z)
  (h₃ : Measurable g)
  (h₄ : Integrable (fun ω ↦ g (F ω)) π)
  (h₅ : F ⟂ᵢ[π] X | Z) :
-- imply
  𝔼[F: π](g F | X, Z) =ᵐ[π] 𝔼[F: π](g F | Z) := by
-- proof
  show π[(fun ω ↦ g (F ω)) | MeasurableSpace.comap (JointRandomSymbol X Z) inferInstance] =ᵐ[π]
    π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)]
  have hmZ : (MeasurableSpace.comap Z inferInstance) ≤ (inferInstance : MeasurableSpace Ω) := h₂.comap_le
  have hJ : Measurable (JointRandomSymbol X Z) := h₁.prodMk h₂
  have hmJ : MeasurableSpace.comap (JointRandomSymbol X Z) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hJ.comap_le
  have hZJ : (MeasurableSpace.comap Z inferInstance) ≤ MeasurableSpace.comap (JointRandomSymbol X Z) inferInstance :=
    (measurable_snd.comp (comap_measurable (JointRandomSymbol X Z))).comap_le
  have hZC : ∀ C : Set δ, MeasurableSet C → MeasurableSet[(MeasurableSpace.comap Z inferInstance)] (Z ⁻¹' C) := fun C hC ↦ ⟨C, hC, rfl⟩
  have hprod := (condIndepFun_iff_condExp_inter_preimage_eq_mul h₀ h₁).1 h₅
  -- `w s = π[1_s | σ(Z)]` takes values in `[0, 1]`
  have hind : ∀ {s : Set Ω}, MeasurableSet s → Integrable (s.indicator fun _ ↦ (1 : ℝ)) π :=
    fun hs ↦ (integrable_const 1).indicator hs
  have hind_le : ∀ s : Set Ω, ∀ᵐ ω ∂π, ‖s.indicator (fun _ ↦ (1 : ℝ)) ω‖ ≤ 1 := fun s ↦
    Filter.Eventually.of_forall fun ω ↦ (norm_indicator_le_norm_self (fun _ ↦ (1 : ℝ)) ω).trans_eq norm_one
  have hw_nn : ∀ s : Set Ω, 0 ≤ᵐ[π] π[s.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] := fun s ↦
    condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω)
  have hw_le : ∀ s : Set Ω, ∀ᵐ ω ∂π, ‖π[s.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] ω‖ ≤ 1 := by
    intro s
    have := ae_bdd_abs_condExp_of_ae_bdd_abs (m := (MeasurableSpace.comap Z inferInstance)) (μ := π) (R := (1 : ℝ)) (f := s.indicator fun _ ↦ (1 : ℝ))
      ((hind_le s).mono fun ω h ↦ by rwa [Real.norm_eq_abs] at h)
    exact this.mono fun ω h ↦ by simpa [Real.norm_eq_abs] using h
  have hw_m : ∀ s : Set Ω, Measurable (π[s.indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)]) := fun s ↦
    (stronglyMeasurable_condExp.mono hmZ).measurable
  -- the law of `F` on `{Z ∈ C} ∩ {X ∈ B}` has density `1_{Z ∈ C} · π[1_{X ∈ B} | σ(Z)]`
  have hstar : ∀ B C, MeasurableSet B → MeasurableSet C →
      ∫ ω in Z ⁻¹' C ∩ X ⁻¹' B, g (F ω) ∂π =
        ∫ ω in Z ⁻¹' C, π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] ω * g (F ω) ∂π := by
    intro B C hB hC
    have hXB : MeasurableSet (X ⁻¹' B) := h₁ hB
    set w := π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] with hw
    set v : Ω → ℝ := (Z ⁻¹' C).indicator w with hv
    have hv_nn : 0 ≤ᵐ[π] v := (hw_nn _).mono fun ω (h : 0 ≤ w ω) ↦ Set.indicator_apply_nonneg fun _ ↦ h
    have hv_int : Integrable v π := integrable_condExp.indicator (h₂ hC)
    have hv_m : Measurable v := (hw_m _).indicator (h₂ hC)
    have hν : (π.restrict (Z ⁻¹' C ∩ X ⁻¹' B)).map F = (π.withDensity fun ω ↦ ENNReal.ofReal (v ω)).map F := by
      ext A hA
      have hFA : MeasurableSet (F ⁻¹' A) := h₀ hA
      have hint1 : Integrable ((F ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w) π :=
        integrable_condExp.bdd_mul (hind hFA).aestronglyMeasurable (hind_le _)
      rw [Measure.map_apply h₀ hA, Measure.map_apply h₀ hA, Measure.restrict_apply hFA,
        withDensity_apply _ hFA,
        ← ofReal_integral_eq_lintegral_ofReal hv_int.integrableOn (ae_restrict_of_ae hv_nn),
        ← ENNReal.ofReal_toReal (measure_ne_top π _), ← measureReal_def]
      congr 1
      calc π.real (F ⁻¹' A ∩ (Z ⁻¹' C ∩ X ⁻¹' B))
          = ∫ ω in Z ⁻¹' C, (F ⁻¹' A ∩ X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) ω ∂π := by
            rw [integral_indicator_const _ (hFA.inter hXB), smul_eq_mul, mul_one,
              measureReal_restrict_apply (hFA.inter hXB)]
            congr 1
            ext ω
            simp only [Set.mem_inter_iff]
            tauto
        _ = ∫ ω in Z ⁻¹' C, π[(F ⁻¹' A ∩ X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] ω ∂π :=
            (setIntegral_condExp hmZ (hind (hFA.inter hXB)) (hZC C hC)).symm
        _ = ∫ ω in Z ⁻¹' C, π[(F ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] ω * w ω ∂π :=
            setIntegral_congr_ae (h₂ hC) ((hprod A B hA hB).mono fun ω h _ ↦ h)
        _ = ∫ ω in Z ⁻¹' C, π[(F ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w | (MeasurableSpace.comap Z inferInstance)] ω ∂π :=
            setIntegral_congr_ae (h₂ hC) ((condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp
              hint1 (hind hFA)).mono fun ω h _ ↦ h.symm)
        _ = ∫ ω in Z ⁻¹' C, ((F ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) * w) ω ∂π :=
            setIntegral_condExp hmZ hint1 (hZC C hC)
        _ = ∫ ω in F ⁻¹' A, v ω ∂π := by
            rw [← integral_indicator (h₂ hC), ← integral_indicator hFA]
            congr 1
            ext ω
            by_cases h1 : ω ∈ Z ⁻¹' C <;> by_cases h2 : ω ∈ F ⁻¹' A <;> simp [v, h1, h2]
    have hd_m : Measurable fun ω ↦ ENNReal.ofReal (v ω) := ENNReal.measurable_ofReal.comp hv_m
    calc ∫ ω in Z ⁻¹' C ∩ X ⁻¹' B, g (F ω) ∂π
        = ∫ b, g b ∂((π.restrict (Z ⁻¹' C ∩ X ⁻¹' B)).map F) :=
          (integral_map h₀.aemeasurable h₃.aestronglyMeasurable).symm
      _ = ∫ b, g b ∂((π.withDensity fun ω ↦ ENNReal.ofReal (v ω)).map F) := by rw [hν]
      _ = ∫ ω, g (F ω) ∂(π.withDensity fun ω ↦ ENNReal.ofReal (v ω)) :=
          integral_map h₀.aemeasurable h₃.aestronglyMeasurable
      _ = ∫ ω, (ENNReal.ofReal (v ω)).toReal • g (F ω) ∂π :=
          integral_withDensity_eq_integral_toReal_smul hd_m
            (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _
      _ = ∫ ω, v ω * g (F ω) ∂π :=
          integral_congr_ae (hv_nn.mono fun ω (h : 0 ≤ v ω) ↦ by simp [ENNReal.toReal_ofReal h])
      _ = ∫ ω in Z ⁻¹' C, w ω * g (F ω) ∂π := by
          rw [← integral_indicator (h₂ hC)]
          congr 1
          ext ω
          by_cases h1 : ω ∈ Z ⁻¹' C <;> simp [v, h1]
  -- rectangles `{X ∈ B} ∩ {Z ∈ C}`
  have hrect : ∀ B C, MeasurableSet B → MeasurableSet C →
      ∫ ω in X ⁻¹' B ∩ Z ⁻¹' C, g (F ω) ∂π = ∫ ω in X ⁻¹' B ∩ Z ⁻¹' C, π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)] ω ∂π := by
    intro B C hB hC
    have hXB : MeasurableSet (X ⁻¹' B) := h₁ hB
    rw [Set.inter_comm, hstar B C hB hC]
    have hwf : Integrable (π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] * fun ω ↦ g (F ω)) π :=
      h₄.bdd_mul integrable_condExp.aestronglyMeasurable (hw_le _)
    have hint2 : Integrable ((X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)]) π :=
      integrable_condExp.bdd_mul (hind hXB).aestronglyMeasurable (hind_le _)
    calc ∫ ω in Z ⁻¹' C, π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] ω * g (F ω) ∂π
        = ∫ ω in Z ⁻¹' C, π[π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] * (fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)] ω ∂π :=
          (setIntegral_condExp hmZ hwf (hZC C hC)).symm
      _ = ∫ ω in Z ⁻¹' C, (π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) | (MeasurableSpace.comap Z inferInstance)] * π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)]) ω ∂π :=
          setIntegral_congr_ae (h₂ hC) ((condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp
            hwf h₄).mono fun ω h _ ↦ h)
      _ = ∫ ω in Z ⁻¹' C, π[(X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)] | (MeasurableSpace.comap Z inferInstance)] ω ∂π :=
          setIntegral_congr_ae (h₂ hC) ((condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp
            hint2 (hind hXB)).mono fun ω h _ ↦ h.symm)
      _ = ∫ ω in Z ⁻¹' C, ((X ⁻¹' B).indicator (fun _ ↦ (1 : ℝ)) * π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)]) ω ∂π :=
          setIntegral_condExp hmZ hint2 (hZC C hC)
      _ = ∫ ω in Z ⁻¹' C ∩ X ⁻¹' B, π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)] ω ∂π := by
          rw [← setIntegral_indicator hXB]
          refine setIntegral_congr_fun (h₂ hC) fun ω _ ↦ ?_
          by_cases h : ω ∈ X ⁻¹' B <;> simp [h]
  -- Dynkin: all of `σ(X, Z)`
  have hkey : ∀ D : Set (γ × δ), MeasurableSet D →
      ∫ ω in JointRandomSymbol X Z ⁻¹' D, g (F ω) ∂π =
        ∫ ω in JointRandomSymbol X Z ⁻¹' D, π[(fun ω ↦ g (F ω)) | (MeasurableSpace.comap Z inferInstance)] ω ∂π := by
    intro D hD
    induction D, hD using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
    | empty => simp
    | basic t ht =>
      obtain ⟨B, hB, C, hC, rfl⟩ := ht
      have : JointRandomSymbol X Z ⁻¹' (B ×ˢ C) = X ⁻¹' B ∩ Z ⁻¹' C := by
        ext ω
        simp [JointRandomSymbol]
      rw [this]
      exact hrect B C hB hC
    | compl t htm ih =>
      rw [Set.preimage_compl, setIntegral_compl (hJ htm) h₄, setIntegral_compl (hJ htm) integrable_condExp,
        ih, integral_condExp hmZ]
    | iUnion f hd hfm ih =>
      rw [Set.preimage_iUnion,
        integral_iUnion (fun i ↦ hJ (hfm i)) (fun i j hij ↦ (hd hij).preimage _) h₄.integrableOn,
        integral_iUnion (fun i ↦ hJ (hfm i)) (fun i j hij ↦ (hd hij).preimage _) integrable_condExp.integrableOn]
      exact tsum_congr ih
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmJ h₄ (fun _ _ _ ↦ integrable_condExp.integrableOn) ?_
    (stronglyMeasurable_condExp.mono hZJ).aestronglyMeasurable).symm
  rintro _ ⟨D, hD, rfl⟩ _
  exact (hkey D hD).symm


-- created on 2026-10-06
