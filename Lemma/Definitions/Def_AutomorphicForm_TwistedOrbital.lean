import Lemma.Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Lemma.Definitions.Def_DedekindDomain_Completion_BaseChange
import Lemma.Definitions.Def_AutomorphicForm_SigmaCentralizer
import Lemma.Definitions.Def_M4aHerbrand_ArchSemilocal

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

section Carrier

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem isTopologicalRing_tensor : IsTopologicalRing (L ⊗[K] A) :=
  IsModuleTopology.Module.topologicalRing A (L ⊗[K] A)

theorem t2Space_tensor [T2Space A] : T2Space (L ⊗[K] A) :=
  IsModuleTopology.t2Space A

theorem locallyCompactSpace_tensor [LocallyCompactSpace A] : LocallyCompactSpace (L ⊗[K] A) :=
  IsModuleTopology.locallyCompactSpaceOfFinite A (M := L ⊗[K] A)

theorem isTopologicalGroup_tensorGL : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  infer_instance

theorem t2Space_tensorGL [T2Space A] : T2Space (GL (Fin 2) (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem locallyCompactSpace_tensorGL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI := locallyCompactSpace_tensor K L A
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → L ⊗[K] A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Carrier

section Borel

variable (R : Type) [CommRing R] [TopologicalSpace R]

@[reducible] def glBorelOf : MeasurableSpace (GL (Fin 2) R) := borel _

theorem borelSpace_glBorelOf : @BorelSpace (GL (Fin 2) R) _ (glBorelOf R) :=
  @BorelSpace.mk _ _ (glBorelOf R) rfl

@[reducible] def centralizerBorel (γ : GL (Fin 2) R) :
    MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) := borel _

end Borel

section Embed

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

def toTensorGL : GL (Fin 2) A →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom

end Embed

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def semiLocalHomeomorph :
    L ⊗[K] v.adicCompletion K ≃ₜ Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L)
    v).toContinuousLinearEquiv.toHomeomorph

def piIntegers : Set (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  Set.univ.pi fun w => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))

theorem isCompact_piIntegers : IsCompact (piIntegers K L v) :=
  isCompact_univ_pi fun w =>
    isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w.1)

theorem isOpen_piIntegers : IsOpen (piIntegers K L v) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact isOpen_set_pi Set.finite_univ fun w _ =>
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w.1

def semiLocalIntegers : Set (L ⊗[K] v.adicCompletion K) :=
  Set.range (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v)

theorem semiLocalIntegers_eq_preimage :
    semiLocalIntegers K L v = semiLocalHomeomorph K L v ⁻¹' piIntegers K L v := by
  have h := HeightOneSpectrum.range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L (𝓞 L) v
  rw [Set.range_comp] at h
  have hinj : Function.Injective (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v) :=
    (HeightOneSpectrum.adicCompletion.baseChange_bijective K L (𝓞 L) v).1
  calc semiLocalIntegers K L v
      = HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ⁻¹'
          (HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v '' semiLocalIntegers K L v) :=
        (Set.preimage_image_eq _ hinj).symm
    _ = semiLocalHomeomorph K L v ⁻¹' piIntegers K L v := by
        rw [semiLocalIntegers, h]; rfl

theorem isCompact_semiLocalIntegers : IsCompact (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (semiLocalHomeomorph K L v).isCompact_preimage.2 (isCompact_piIntegers K L v)

theorem isOpen_semiLocalIntegers : IsOpen (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (isOpen_piIntegers K L v).preimage (semiLocalHomeomorph K L v).continuous

omit [NumberField L] in
theorem zero_mem_semiLocalIntegers : (0 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨0, map_zero _⟩

omit [NumberField L] in
theorem one_mem_semiLocalIntegers : (1 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨1, map_one _⟩

def IsSemiLocalTestFn (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant φv ∧ HasCompactSupport φv

theorem isSemiLocalTestFn_zero : IsSemiLocalTestFn K L v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

def semiLocalIntegralSet : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  integralUnitsSet (semiLocalIntegers K L v)

omit [NumberField L] in
theorem one_mem_semiLocalIntegralSet :
    (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v :=
  one_mem_integralUnitsSet (zero_mem_semiLocalIntegers K L v) (one_mem_semiLocalIntegers K L v)

theorem isCompact_semiLocalIntegralSet : IsCompact (semiLocalIntegralSet K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  exact isCompact_integralUnitsSet (isCompact_semiLocalIntegers K L v)

theorem isOpen_semiLocalIntegralSet : IsOpen (semiLocalIntegralSet K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  exact isOpen_integralUnitsSet (isOpen_semiLocalIntegers K L v)

def semiLocalIntegralCompacts : PositiveCompacts (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := semiLocalIntegralSet K L v
  isCompact' := isCompact_semiLocalIntegralSet K L v
  interior_nonempty' := by
    rw [(isOpen_semiLocalIntegralSet K L v).interior_eq]
    exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩

theorem isSemiLocalTestFn_indicator_semiLocalIntegralSet :
    IsSemiLocalTestFn K L v ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact ⟨isLocallyConstant_indicator_one (isOpen_semiLocalIntegralSet K L v)
      (isCompact_semiLocalIntegralSet K L v).isClosed,
    HasCompactSupport.intro (isCompact_semiLocalIntegralSet K L v) fun _ hg => by simp [hg]⟩

def semiLocalHaar :
    @Measure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (glBorelOf (L ⊗[K] v.adicCompletion K)) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure (semiLocalIntegralCompacts K L v)

theorem isHaarMeasure_semiLocalHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) _ _
      (glBorelOf (L ⊗[K] v.adicCompletion K)) (semiLocalHaar K L v) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  exact Measure.isHaarMeasure_haarMeasure _

theorem semiLocalHaar_semiLocalIntegralSet :
    semiLocalHaar K L v (semiLocalIntegralSet K L v) = 1 := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure_self

end SemiLocal

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

def sigmaTensor : L ⊗[K] A →+* L ⊗[K] A :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)).toRingHom

def sigmaGL : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ)

def normString (δ : GL (Fin 2) (L ⊗[K] A)) : GL (Fin 2) (L ⊗[K] A) :=
  ((List.range (Module.finrank K L)).map fun i => (⇑(sigmaGL K L A σ))^[i] δ).prod

def IsSigmaConjugate (δ δ' : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  ∃ x : GL (Fin 2) (L ⊗[K] A), δ' = x⁻¹ * δ * sigmaGL K L A σ x

theorem isSigmaConjugate_self (δ : GL (Fin 2) (L ⊗[K] A)) : IsSigmaConjugate K L A σ δ δ :=
  ⟨1, by simp⟩

def IsNormConjugator (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  toTensorGL K L A γ = y⁻¹ * normString K L A σ δ * y

def IsNormOf (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A)) : Prop :=
  ∃ y, IsNormConjugator K L A σ γ δ y

abbrev twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) : Subgroup (GL (Fin 2) (L ⊗[K] A)) :=
  sigmaCentralizer (sigmaGL K L A σ) δ

end Twist

section TwistedBorel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

@[reducible] def twistedCentralizerBorel (δ : GL (Fin 2) (L ⊗[K] A)) :
    MeasurableSpace (twistedCentralizer K L A σ δ) := borel _

end TwistedBorel

section Untwisted

variable (A : Type) [CommRing A] [TopologicalSpace A]

def IsSectionFnOn (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (w : GL (Fin 2) A → ℝ) : Prop :=
  letI := glBorelOf A
  letI := centralizerBorel A γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, f (x⁻¹ * γ * x) ≠ 0 →
      ∫ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), w (t * x) ∂τ = 1

def IsOrbitalIntegralOn (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (f : GL (Fin 2) A → ℂ) (I : ℂ) : Prop :=
  letI := glBorelOf A
  ∃ w : GL (Fin 2) A → ℝ, IsSectionFnOn A γ τ f w ∧ I = ∫ x, f (x⁻¹ * γ * x) * (w x : ℂ) ∂μ

theorem isSectionFnOn_zero (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsSectionFnOn A γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

theorem isOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFnOn_zero A γ τ, by simp⟩

theorem not_isOrbitalIntegralOn_zero_one (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    ¬ IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)

def IsTwistedSectionFnOn (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ δ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) ≠ 0 →
      ∫ t : twistedCentralizer K L A σ δ, w (t * x) ∂τ' = 1

def IsTwistedOrbitalIntegralOn (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I' : ℂ) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ w ∧
    I' = ∫ x, φ (x⁻¹ * δ * sigmaGL K L A σ x) * (w x : ℂ) ∂μ

theorem isTwistedSectionFnOn_zero (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedSectionFnOn K L A σ δ τ' (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

theorem isTwistedOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 0 :=
  ⟨fun _ => 0, isTwistedSectionFnOn_zero K L A σ δ τ', by simp⟩

theorem not_isTwistedOrbitalIntegralOn_zero_one
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    ¬ IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

def Coupled (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) : Prop :=
  letI := glBorelOf (L ⊗[K] A)
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  Measure.map (fun t : twistedCentralizer K L A σ δ => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) τ' =
    Measure.map
      (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => toTensorGL K L A (t : GL (Fin 2) A))
      τ

def AreMatchingOn (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (f : GL (Fin 2) A → ℂ) : Prop :=
  (∀ δ : GL (Fin 2) (L ⊗[K] A), IsRegularSemisimple (normString K L A σ δ) →
    ∀ γ : GL (Fin 2) A, IsRegularSemisimple γ →
    ∀ y : GL (Fin 2) (L ⊗[K] A), IsNormConjugator K L A σ γ δ y →
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' →
      Coupled K L A σ γ δ y τ τ' →
      ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L A σ μL δ τ' φ I' →
        IsOrbitalIntegralOn A μK γ τ f I → I' = I) ∧
  (∀ γ : GL (Fin 2) A, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf K L A σ γ δ) →
    ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ →
      ∀ I : ℂ, IsOrbitalIntegralOn A μK γ τ f I → I = 0)

theorem areMatchingOn_zero (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (μK : @Measure (GL (Fin 2) A) (glBorelOf A)) :
    AreMatchingOn K L A σ μL μK (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun δ _ γ _ y _ τ τ' _ _ _ I I' hI' hI => ?_, fun γ _ _ τ _ I hI => ?_⟩
  · obtain ⟨w', -, rfl⟩ := hI'
    obtain ⟨w, -, rfl⟩ := hI
    simp
  · obtain ⟨w, -, rfl⟩ := hI
    simp

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem isOrbitalIntegralOn_localHaar_iff (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) :
    IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ fv I ↔
      IsOrbitalIntegral K v γ τ fv I :=
  Iff.rfl

def IsTwistedOrbitalIntegral (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I' : ℂ) : Prop :=
  IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φv I'

theorem isTwistedOrbitalIntegral_zero (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 0 := by
  unfold IsTwistedOrbitalIntegral
  exact isTwistedOrbitalIntegralOn_zero K L _ σ _ δ τ'

theorem not_isTwistedOrbitalIntegral_zero_one (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    ¬ IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 1 := by
  unfold IsTwistedOrbitalIntegral
  exact not_isTwistedOrbitalIntegralOn_zero_one K L _ σ _ δ τ'

def AreMatchingLocal (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  AreMatchingOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) (localHaar K v) φv fv

theorem areMatchingLocal_zero : AreMatchingLocal K L v σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingLocal
  exact areMatchingOn_zero K L _ σ _ _

end FinitePlaces

section Archimedean

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L)

def archHaarK : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (glBorelOf (InfiniteAdeleRing K)) := by
  letI := glBorelOf (InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact Measure.haar

def archHaarL :
    @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  exact Measure.haar

def archIdent : L ⊗[K] InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.toRingHom

def archIdentGL : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →* GL (Fin 2) (InfiniteAdeleRing L) :=
  Matrix.GeneralLinearGroup.map (archIdent K L)

def AreMatchingArch (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) : Prop :=
  AreMatchingOn K L (InfiniteAdeleRing K) σ (archHaarL K L) (archHaarK K) (φa ∘ archIdentGL K L) fa

theorem areMatchingArch_zero : AreMatchingArch K L σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingArch
  exact areMatchingOn_zero K L _ σ _ _

end Archimedean

section AboveTier

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def semiLocalEval (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 L) L →+* L ⊗[K] v.adicCompletion K :=
  (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm.toRingEquiv.toRingHom.comp
    (RingHom.pi fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1)

def semiLocalComponent (v : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (semiLocalEval K L v)

variable (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))) (S : Finset (HeightOneSpectrum (𝓞 K)))

def IsSemiLocalFactorization (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  IsArchTestFactor L φa ∧ IsFinTestFactor L φf ∧ (∀ v ∈ S, IsSemiLocalTestFn K L v (φS v)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) →
      φf h = ∏ v ∈ S, φS v (semiLocalComponent K L v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
    (∃ v ∉ S, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v) → φf h = 0) ∧
  ∀ g, φ g = φa (AdelicLevel.glArch (𝓞 L) L g) * φf (AdelicLevel.glFin (𝓞 L) L g)

def IsUnitFactorizableAbove (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) : Prop :=
  IsBiInvariantUnder L U φ ∧ ∃ φa φf φS, IsSemiLocalFactorization K L S φ φa φf φS

theorem IsUnitFactorizableAbove.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))} (hUV : U ≤ V)
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAbove K L V S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  ⟨hφ.1.mono L hUV, hφ.2⟩

theorem isSemiLocalFactorization_zero (hS : S.Nonempty) :
    IsSemiLocalFactorization K L S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero L, isFinTestFactor_zero L, fun v _ => isSemiLocalTestFn_zero K L v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm

theorem isUnitFactorizableAbove_zero (hS : S.Nonempty) : IsUnitFactorizableAbove K L U S (fun _ => 0) :=
  ⟨fun _ _ _ => ⟨rfl, rfl⟩, _, _, _, isSemiLocalFactorization_zero K L S hS⟩

end AboveTier

section AboveTierRefined

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
  (S : Finset (HeightOneSpectrum (𝓞 K)))

def IsUnitFactorizableAboveOfType (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) : Prop :=
  IsUnitFactorizableAbove K L U S φ ∧ IsArchBiFinite L tys φ

variable {K L tys U S}

theorem IsUnitFactorizableAboveOfType.isUnitFactorizableAbove
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  hφ.1

theorem IsUnitFactorizableAboveOfType.isArchBiFinite
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsArchBiFinite L tys φ :=
  hφ.2

theorem IsUnitFactorizableAboveOfType.mono {V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))}
    (hUV : U ≤ V) {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys V S φ) : IsUnitFactorizableAboveOfType K L tys U S φ :=
  ⟨hφ.1.mono K L S hUV, hφ.2⟩

theorem IsUnitFactorizableAboveOfType.mono_type {tys' : ArchTypeFamily L} (h : tys.IsContainedIn L tys')
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAboveOfType K L tys' U S φ :=
  ⟨hφ.1, hφ.2.mono L h⟩

variable (K L tys U S)

theorem isUnitFactorizableAboveOfType_zero (hS : S.Nonempty) :
    IsUnitFactorizableAboveOfType K L tys U S (fun _ => 0) :=
  ⟨isUnitFactorizableAbove_zero K L U S hS, isArchBiFinite_zero L tys⟩

end AboveTierRefined

section BelowTier

variable (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

def IsUnitFactorization (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
      ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
  (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
    (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
  ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

theorem isUnitFactorizableAt_iff (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsUnitFactorizableAt K U S f ↔
      IsBiInvariantUnder K U f ∧ ∃ fa ff fS, IsUnitFactorization K S f fa ff fS :=
  Iff.rfl

theorem isUnitFactorization_zero (hS : S.Nonempty) :
    IsUnitFactorization K S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero K, isFinTestFactor_zero K, fun v _ => isLocalTestFn_zero K v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm

end BelowTier

section Global

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))

def AreMatchingAt (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    Prop :=
  ∃ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsSemiLocalFactorization K L S φ φa φf φS ∧ IsUnitFactorization K S f fa ff fS ∧
    AreMatchingArch K L σ φa fa ∧ ∀ v ∈ S, AreMatchingLocal K L v σ (φS v) (fS v)

theorem areMatchingAt_zero (hS : S.Nonempty) : AreMatchingAt K L σ S (fun _ => 0) (fun _ => 0) :=
  ⟨_, _, _, _, _, _, isSemiLocalFactorization_zero K L S hS, isUnitFactorization_zero K S hS,
    areMatchingArch_zero K L σ, fun v _ => areMatchingLocal_zero K L v σ⟩

end Global

end AutomorphicForm

end
