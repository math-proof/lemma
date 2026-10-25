import Lemma.AutomorphicForm.CuspidalConstituent
import Lemma.NumberField.TateGlobalZeta
import Structure.AutomorphicForm_CuspidalSpectrumCarrier

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm

namespace CuspidalSpectrum

variable (F : Type) [Field F] [NumberField F]


@[simp] theorem mem_detNormSlab (α β : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ detNormSlab F α β ↔
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β := Iff.rfl

theorem detNormSlab_def (α β : ℝ) : detNormSlab F α β =
    {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} := rfl


theorem IsSlabFundamentalDomain.pos_right {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (h : IsSlabFundamentalDomain F α β Φ₀) : 0 < β := h.pos.trans h.lt


@[simp] theorem fdPins_eq (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    fdPins F Φ₀ = productionPinsOf F Φ₀ (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) (adelicBox F) := rfl
@[simp] theorem fdPins_Z (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).Z = ⊤ := rfl
@[simp] theorem fdPins_D (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).D = Φ₀ := rfl
@[simp] theorem fdPins_mS (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).mS = glBorel (Fin 2) (𝓞 F) F := rfl
@[simp] theorem fdPins_μ (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl
@[simp] theorem fdPins_U (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    (fdPins F Φ₀).U = fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl
@[simp] theorem fdPins_gen (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).gen = fun v => heckeGen (𝓞 F) F v := rfl
@[simp] theorem fdPins_nS (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : (fdPins F Φ₀).nS = adeleBorel (𝓞 F) F := rfl
@[simp] theorem fdPins_ν (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    (fdPins F Φ₀).ν = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) := rfl

def HasModulus (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) : Prop :=
  ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ

theorem hasModulus_iff (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) :
    HasModulus F ξ σ ↔ ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) ^ σ := Iff.rfl

theorem hasModulus_iff_units (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) :
    HasModulus F ξ σ ↔ ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm F z ^ σ :=
  ⟨fun h z => h ⟨z, Subgroup.mem_top z⟩, fun h z => h z⟩


theorem weight_def (σ : ℝ) (x : AdelicGL2 (𝓞 F) F) :
    weight F σ x = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) := rfl


theorem weightedMeasure_def (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) :
    weightedMeasure F Φ₀ σ =
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀).withDensity fun x => ENNReal.ofReal (weight F σ x) := rfl


theorem mem_memberSubmodule_iff (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ memberSubmodule F Φ₀ ξ ↔ IsAutomorphicFnAt F (fdPins F Φ₀) ξ φ := Iff.rfl

theorem mem_memberSubmodule_iff' (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ memberSubmodule F Φ₀ ξ ↔
      IsLsXiFunction (𝓞 F) F ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
  isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ


theorem continuous_unipotentGL2_adele :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 F) F,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -x; 0, 1] :=
      fun x => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

theorem integrable_constantTermIntegrand_fdPins (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
    Integrable (constantTermIntegrand unipotentGL2 φ g) (fdPins F Φ₀).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  show Integrable (constantTermIntegrand unipotentGL2 φ g)
    (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
  have hcont : Continuous (constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ g) :=
    hφ.comp ((continuous_unipotentGL2_adele F).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hint : IntegrableOn (constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) φ g) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

def cuspMemberSubmodule (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | IsSmoothCuspAutomorphicFnAt F (fdPins F Φ₀) ξ φ ∧ Continuous φ}
  zero_mem' := ⟨isSmoothCuspAutomorphicFnAt_zero F (fdPins F Φ₀) ξ, continuous_const⟩
  add_mem' := fun {a b} ha hb => by
    refine ⟨⟨⟨(memberSubmodule F Φ₀ ξ).add_mem ha.1.1.1 hb.1.1.1, fun g => ?_⟩, ?_⟩, ha.2.add hb.2⟩
    ·
      letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
      have hia := integrable_constantTermIntegrand_fdPins F Φ₀ ha.2 g
      have hib := integrable_constantTermIntegrand_fdPins F Φ₀ hb.2 g
      have h0a := ha.1.1.2 g
      have h0b := hb.1.1.2 g
      unfold constantTerm at h0a h0b ⊢
      have : constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) (a + b) g
          = fun q => constantTermIntegrand unipotentGL2 a g q + constantTermIntegrand unipotentGL2 b g q := rfl
      rw [this, integral_add hia hib, h0a, h0b, add_zero]
    ·
      refine Subgroup.isOpen_mono ?_ (FLT.SmoothVectors.isOpen_coe_inf_stabilizer ha.1.2 hb.1.2)
      intro u hu
      obtain ⟨hua, hub⟩ := Subgroup.mem_inf.mp hu
      rw [MulAction.mem_stabilizer_iff] at hua hub ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hua
      have h2 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hub
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 h2 ⊢
      show a (x * ↑u) + b (x * ↑u) = a x + b x
      rw [h1, h2]
  smul_mem' := fun c {a} ha => by
    refine ⟨⟨⟨(memberSubmodule F Φ₀ ξ).smul_mem c ha.1.1.1, fun g => ?_⟩, ?_⟩, ha.2.const_smul c⟩
    · letI : MeasurableSpace (AdeleRing (𝓞 F) F) := (fdPins F Φ₀).nS
      have h0a := ha.1.1.2 g
      unfold constantTerm at h0a ⊢
      have : constantTermIntegrand (unipotentGL2 (R := AdeleRing (𝓞 F) F)) (c • a) g
          = fun q => c * constantTermIntegrand unipotentGL2 a g q := rfl
      rw [this, integral_const_mul, h0a, mul_zero]
    · refine Subgroup.isOpen_mono ?_ ha.1.2
      intro u hua
      rw [MulAction.mem_stabilizer_iff] at hua ⊢
      refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
      have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hua
      simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
        FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1 ⊢
      show c • a (x * ↑u) = c • a x
      rw [h1]


def pairing (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) (a b : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  ∫ x in Φ₀, a x * conj (b x) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

theorem pairing_def (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (σ : ℝ) (a b : AdelicGL2 (𝓞 F) F → ℂ) :
    pairing F Φ₀ σ a b = ∫ x in Φ₀, a x * conj (b x) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := rfl

def cuspSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : Submodule ℂ (Carrier F Φ₀ σ) :=
  (Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))).topologicalClosure

def toCuspSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ↥(cuspMemberSubmodule F Φ₀ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  LinearMap.codRestrict _ ((toCarrier F hΦ₀ σ ξ).comp
      (Submodule.inclusion (show cuspMemberSubmodule F Φ₀ ξ ≤ memberSubmodule F Φ₀ ξ from fun _ h => h.1.1.1)))
    (fun φ => Submodule.le_topologicalClosure _
      ⟨Submodule.inclusion (show cuspMemberSubmodule F Φ₀ ξ ≤ memberSubmodule F Φ₀ ξ from fun _ h => h.1.1.1) φ,
        φ.2, rfl⟩)

theorem toCuspSubcarrier_apply_coe {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) :
    (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨φ, φ.2.1.1.1⟩ := rfl

def cuspLevelSubcarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F)) : Submodule ℂ (Carrier F Φ₀ σ) :=
  (Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
        (cuspMemberSubmodule F Φ₀ ξ ⊓
          CuspidalConstituent.levelInvariantSubmodule F (fdPins F Φ₀) N))).topologicalClosure


def flat (σ : ℝ) (g : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun y => conj (g y⁻¹) *
    ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)

end CuspidalSpectrum

end AutomorphicForm

end
