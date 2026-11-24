module
public import Theorem.Matrix.UnitFactorizableOfType
public import Theorem.ContinuousMap.topologicalRing
public import Theorem.LinearMap.t2Space
public import Theorem.ContinuousMap.locallyCompactSpaceOfFinite
public import Instance.DedekindDomain_Completion_BaseChange
public import Theorem.Kernel.SigmaCentralizer
public import Def.M4aHerbrand_ArchSemilocal
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct RingHom
open scoped TensorProduct.RightActions


public section

noncomputable section

namespace AutomorphicForm

section Carrier

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

end Carrier

section Borel

variable (R : Type) [CommRing R] [TopologicalSpace R]

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

def semiLocalIntegers : Set (L ⊗[K] v.adicCompletion K) :=
  Set.range (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v)

def IsSemiLocalTestFn (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant φv ∧ HasCompactSupport φv

def semiLocalIntegralSet : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
  integralUnitsSet (semiLocalIntegers K L v)

omit [NumberField L] in
def semiLocalIntegralCompacts : PositiveCompacts (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) where
  carrier := semiLocalIntegralSet K L v
  isCompact' := isCompact_semiLocalIntegralSet K L v
  interior_nonempty' := by
    rw [(isOpen_semiLocalIntegralSet K L v).interior_eq]
    exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩

def semiLocalHaar :
    @Measure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (glBorelOf (L ⊗[K] v.adicCompletion K)) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure (semiLocalIntegralCompacts K L v)

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

end Twisted

section FinitePlaces

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

def IsTwistedOrbitalIntegral (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (I' : ℂ) : Prop :=
  IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) δ τ' φv I'

def AreMatchingLocal (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  AreMatchingOn K L (v.adicCompletion K) σ (semiLocalHaar K L v) (localHaar K v) φv fv

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

end AboveTier

section AboveTierRefined

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
  (S : Finset (HeightOneSpectrum (𝓞 K)))

def IsUnitFactorizableAboveOfType (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) : Prop :=
  IsUnitFactorizableAbove K L U S φ ∧ IsArchBiFinite L tys φ

variable {K L tys U S}

variable (K L tys U S)

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

end Global

end AutomorphicForm

end
