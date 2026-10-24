import Lemma.Definitions.Def_NumberField_AdelicHaar
import Lemma.Definitions.Def_NumberField_AdelicBox
import Lemma.Definitions.Def_M4aHerbrand_OpenMappingBridge

namespace M4aHerbrand.Bridge

open NumberField IsDedekindDomain TensorProduct

section Infinite

variable (K : Type*) [Field K]

instance sigmaCompactSpace_completion (v : InfinitePlace K) : SigmaCompactSpace v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace

instance sigmaCompactSpace_infiniteAdeleRing [NumberField K] : SigmaCompactSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (SigmaCompactSpace ((v : InfinitePlace K) → v.Completion))

end Infinite

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] in

theorem countable_of_free_finite_int [Module.Free ℤ R] [Module.Finite ℤ R] : Countable R :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℤ R).equivFun.toEquiv.symm

theorem iUnion_smul_integralFiniteAdeles :
    ⋃ s : R, (fun z => algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ * z) ''
      NumberField.AdelicBox.integralFiniteAdeles R K = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles R K y
  refine Set.mem_iUnion.mpr ⟨s, _, hs, ?_⟩
  have hsK : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0
  show algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ *
      (algebraMap R (FiniteAdeleRing R K) s * y) = y
  rw [← mul_assoc, IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K) s, ← map_mul,
    inv_mul_cancel₀ hsK, map_one, one_mul]

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_integralFiniteAdeles :
    IsCompact (NumberField.AdelicBox.integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing R K) := by
  haveI : Countable R := countable_of_free_finite_int R
  refine ⟨?_⟩
  rw [← iUnion_smul_integralFiniteAdeles R K]
  exact isSigmaCompact_iUnion_of_isCompact _ fun s =>
    (isCompact_integralFiniteAdeles R K).image (continuous_const.mul continuous_id)

instance sigmaCompactSpace_adeleRing [NumberField K] : SigmaCompactSpace (AdeleRing R K) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))

theorem locallyCompactSpace_adeleRing [NumberField K] : LocallyCompactSpace (AdeleRing R K) :=
  inferInstance

end Finite

section Conjugation

variable (A K B L : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B] [IsDedekindDomain B] [Field L] [NumberField L] [Algebra B L] [IsFractionRing B L]
  [Module.Free ℤ B] [Module.Finite ℤ B] [Algebra K L]

theorem continuous_conjAct_of_continuous_of_free
    [Algebra (AdeleRing A K) (AdeleRing B L)]
    (hβ : Continuous (algebraMap (AdeleRing A K) (AdeleRing B L)))
    (te : ((AdeleRing A K) ⊗[K] L) ≃ₐ[AdeleRing A K] AdeleRing B L) (σ : L ≃ₐ[K] L) :
    Continuous (conjAct A K B L te σ) :=
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  continuous_conjAct_of_continuous A K B L hβ te σ

theorem isModuleTopology_adeleRing_of_free
    [Algebra (AdeleRing A K) (AdeleRing B L)]
    (hβ : Continuous (algebraMap (AdeleRing A K) (AdeleRing B L)))
    (te : ((AdeleRing A K) ⊗[K] L) ≃ₐ[AdeleRing A K] AdeleRing B L) :
    IsModuleTopology (AdeleRing A K) (AdeleRing B L) :=
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  isModuleTopology_adeleRing_of_continuous A K B L hβ te

end Conjugation

section ConjugationRingOfIntegers

variable (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]

theorem continuous_conjAct_of_continuous_numberField
    [Algebra (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F)]
    (hβ : Continuous (algebraMap (AdeleRing (𝓞 E) E) (AdeleRing (𝓞 F) F)))
    (te : ((AdeleRing (𝓞 E) E) ⊗[E] F) ≃ₐ[AdeleRing (𝓞 E) E] AdeleRing (𝓞 F) F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct (𝓞 E) E (𝓞 F) F te σ) :=
  continuous_conjAct_of_continuous_of_free (𝓞 E) E (𝓞 F) F hβ te σ

end ConjugationRingOfIntegers

end M4aHerbrand.Bridge
