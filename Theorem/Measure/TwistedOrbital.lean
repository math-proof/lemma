module

public import Theorem.Matrix.UnitFactorizableOfType
public import Theorem.ContinuousMap.topologicalRing
public import Theorem.LinearMap.t2Space
public import Theorem.ContinuousMap.locallyCompactSpaceOfFinite
public import Instance.DedekindDomain_Completion_BaseChange
public import Theorem.Kernel.SigmaCentralizer
public import Def.M4aHerbrand_ArchSemilocal

public noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct RingHom
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

section Carrier

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

public theorem isTopologicalRing_tensor : IsTopologicalRing (L ⊗[K] A) :=
  ContinuousMap.topologicalRing (R := A) (D := L ⊗[K] A)


public theorem t2Space_tensor [T2Space A] : T2Space (L ⊗[K] A) :=
  LinearMap.t2Space (R := A)


public theorem locallyCompactSpace_tensor [LocallyCompactSpace A] : LocallyCompactSpace (L ⊗[K] A) :=
  ContinuousMap.locallyCompactSpaceOfFinite (R := A) (M := L ⊗[K] A)


public theorem isTopologicalGroup_tensorGL : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  infer_instance


public theorem t2Space_tensorGL [T2Space A] : T2Space (GL (Fin 2) (L ⊗[K] A)) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := t2Space_tensor K L A
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → L ⊗[K] A))
  exact Units.isEmbedding_embedProduct.t2Space


public theorem locallyCompactSpace_tensorGL [T2Space A] [LocallyCompactSpace A] :
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


public theorem borelSpace_glBorelOf : @BorelSpace (GL (Fin 2) R) _ (glBorelOf R) :=
  @BorelSpace.mk _ _ (glBorelOf R) rfl


public theorem isCompact_piIntegers : IsCompact (piIntegers K L v) :=
  isCompact_univ_pi fun w =>
    isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w.1)


public theorem isOpen_piIntegers : IsOpen (piIntegers K L v) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact isOpen_set_pi Set.finite_univ fun w _ =>
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 L) L).out w.1


public theorem semiLocalIntegers_eq_preimage :
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


public theorem isCompact_semiLocalIntegers : IsCompact (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (semiLocalHomeomorph K L v).isCompact_preimage.2 (isCompact_piIntegers K L v)


public theorem isOpen_semiLocalIntegers : IsOpen (semiLocalIntegers K L v) := by
  rw [semiLocalIntegers_eq_preimage]
  exact (isOpen_piIntegers K L v).preimage (semiLocalHomeomorph K L v).continuous

omit [NumberField L] in

public theorem zero_mem_semiLocalIntegers : (0 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨0, map_zero _⟩

omit [NumberField L] in

public theorem one_mem_semiLocalIntegers : (1 : L ⊗[K] v.adicCompletion K) ∈ semiLocalIntegers K L v :=
  ⟨1, map_one _⟩


public theorem isSemiLocalTestFn_zero : IsSemiLocalTestFn K L v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩


public theorem one_mem_semiLocalIntegralSet :
    (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ semiLocalIntegralSet K L v :=
  one_mem_integralUnitsSet (zero_mem_semiLocalIntegers K L v) (one_mem_semiLocalIntegers K L v)


public theorem isCompact_semiLocalIntegralSet : IsCompact (semiLocalIntegralSet K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  exact isCompact_integralUnitsSet (isCompact_semiLocalIntegers K L v)


public theorem isOpen_semiLocalIntegralSet : IsOpen (semiLocalIntegralSet K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  exact isOpen_integralUnitsSet (isOpen_semiLocalIntegers K L v)


public theorem isSemiLocalTestFn_indicator_semiLocalIntegralSet :
    IsSemiLocalTestFn K L v ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI : R1Space (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := T2Space.r1Space
  exact ⟨isLocallyConstant_indicator_one (isOpen_semiLocalIntegralSet K L v)
      (isCompact_semiLocalIntegralSet K L v).isClosed,
    HasCompactSupport.intro (isCompact_semiLocalIntegralSet K L v) fun _ hg => by simp [hg]⟩


public theorem isHaarMeasure_semiLocalHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) _ _
      (glBorelOf (L ⊗[K] v.adicCompletion K)) (semiLocalHaar K L v) := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  exact Measure.isHaarMeasure_haarMeasure _


public theorem semiLocalHaar_semiLocalIntegralSet :
    semiLocalHaar K L v (semiLocalIntegralSet K L v) = 1 := by
  letI := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  exact Measure.haarMeasure_self

end SemiLocal

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)


public theorem isSigmaConjugate_self (δ : GL (Fin 2) (L ⊗[K] A)) : IsSigmaConjugate K L A σ δ δ :=
  ⟨1, by simp⟩


public theorem isSectionFnOn_zero (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsSectionFnOn A γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩


public theorem isOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFnOn_zero A γ τ, by simp⟩


public theorem not_isOrbitalIntegralOn_zero_one (μ : @Measure (GL (Fin 2) A) (glBorelOf A))
    (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ)) :
    ¬ IsOrbitalIntegralOn A μ γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end Untwisted

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] (σ : L ≃ₐ[K] L)


public theorem isTwistedSectionFnOn_zero (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedSectionFnOn K L A σ δ τ' (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩


public theorem isTwistedOrbitalIntegralOn_zero (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 0 :=
  ⟨fun _ => 0, isTwistedSectionFnOn_zero K L A σ δ τ', by simp⟩


public theorem not_isTwistedOrbitalIntegralOn_zero_one
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A))) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ)) :
    ¬ IsTwistedOrbitalIntegralOn K L A σ μ δ τ' (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h


public theorem areMatchingOn_zero (μL : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
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


public theorem isOrbitalIntegralOn_localHaar_iff (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) :
    IsOrbitalIntegralOn (v.adicCompletion K) (localHaar K v) γ τ fv I ↔
      IsOrbitalIntegral K v γ τ fv I :=
  Iff.rfl


public theorem isTwistedOrbitalIntegral_zero (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 0 := by
  unfold IsTwistedOrbitalIntegral
  exact isTwistedOrbitalIntegralOn_zero K L _ σ _ δ τ'


public theorem not_isTwistedOrbitalIntegral_zero_one (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : @Measure (twistedCentralizer K L (v.adicCompletion K) σ δ)
      (twistedCentralizerBorel K L (v.adicCompletion K) σ δ)) :
    ¬ IsTwistedOrbitalIntegral K L v σ δ τ' (fun _ => 0) 1 := by
  unfold IsTwistedOrbitalIntegral
  exact not_isTwistedOrbitalIntegralOn_zero_one K L _ σ _ δ τ'


public theorem areMatchingLocal_zero : AreMatchingLocal K L v σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingLocal
  exact areMatchingOn_zero K L _ σ _ _

end FinitePlaces

section Archimedean

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L)


public theorem areMatchingArch_zero : AreMatchingArch K L σ (fun _ => 0) (fun _ => 0) := by
  unfold AreMatchingArch
  exact areMatchingOn_zero K L _ σ _ _

end Archimedean

section AboveTier

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


public theorem IsUnitFactorizableAbove.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))} (hUV : U ≤ V)
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAbove K L V S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  ⟨hφ.1.mono L hUV, hφ.2⟩


public theorem isSemiLocalFactorization_zero (hS : S.Nonempty) :
    IsSemiLocalFactorization K L S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero L, isFinTestFactor_zero L, fun v _ => isSemiLocalTestFn_zero K L v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm


public theorem isUnitFactorizableAbove_zero (hS : S.Nonempty) : IsUnitFactorizableAbove K L U S (fun _ => 0) :=
  ⟨fun _ _ _ => ⟨rfl, rfl⟩, _, _, _, isSemiLocalFactorization_zero K L S hS⟩

end AboveTier

section AboveTierRefined

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
  (S : Finset (HeightOneSpectrum (𝓞 K)))


public theorem IsUnitFactorizableAboveOfType.isUnitFactorizableAbove
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAbove K L U S φ :=
  hφ.1


public theorem IsUnitFactorizableAboveOfType.isArchBiFinite
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsArchBiFinite L tys φ :=
  hφ.2


public theorem IsUnitFactorizableAboveOfType.mono {V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L))}
    (hUV : U ≤ V) {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys V S φ) : IsUnitFactorizableAboveOfType K L tys U S φ :=
  ⟨hφ.1.mono K L S hUV, hφ.2⟩


public theorem IsUnitFactorizableAboveOfType.mono_type {tys' : ArchTypeFamily L} (h : tys.IsContainedIn L tys')
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) :
    IsUnitFactorizableAboveOfType K L tys' U S φ :=
  ⟨hφ.1, hφ.2.mono L h⟩

variable (K L tys U S)


public theorem isUnitFactorizableAboveOfType_zero (hS : S.Nonempty) :
    IsUnitFactorizableAboveOfType K L tys U S (fun _ => 0) :=
  ⟨isUnitFactorizableAbove_zero K L U S hS, isArchBiFinite_zero L tys⟩

end AboveTierRefined

section BelowTier

variable (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))


public theorem isUnitFactorizableAt_iff (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsUnitFactorizableAt K U S f ↔
      IsBiInvariantUnder K U f ∧ ∃ fa ff fS, IsUnitFactorization K S f fa ff fS :=
  Iff.rfl


public theorem isUnitFactorization_zero (hS : S.Nonempty) :
    IsUnitFactorization K S (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) := by
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨isArchTestFactor_zero K, isFinTestFactor_zero K, fun v _ => isLocalTestFn_zero K v,
    fun h _ => ?_, fun _ _ => rfl, fun _ => by simp⟩
  exact (Finset.prod_eq_zero hv₀ rfl).symm

end BelowTier

section Global

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (S : Finset (HeightOneSpectrum (𝓞 K)))


public theorem areMatchingAt_zero (hS : S.Nonempty) : AreMatchingAt K L σ S (fun _ => 0) (fun _ => 0) :=
  ⟨_, _, _, _, _, _, isSemiLocalFactorization_zero K L S hS, isUnitFactorization_zero K S hS,
    areMatchingArch_zero K L σ, fun v _ => areMatchingLocal_zero K L v σ⟩

end Global

end AutomorphicForm

end
