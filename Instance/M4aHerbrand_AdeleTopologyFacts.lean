-- Carved from Lemma/Definitions/Def_M4aHerbrand_AdeleTopologyFacts.lean: instance decls only.
import Instance.NumberField_AdelicHaar
import Instance.M4aHerbrand_OpenMappingBridge

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


instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing R K) := by
  haveI : Countable R := countable_of_free_finite_int R
  refine ⟨?_⟩
  rw [← iUnion_smul_integralFiniteAdeles R K]
  exact isSigmaCompact_iUnion_of_isCompact _ fun s =>
    (isCompact_integralFiniteAdeles R K).image (continuous_const.mul continuous_id)

instance sigmaCompactSpace_adeleRing [NumberField K] : SigmaCompactSpace (AdeleRing R K) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))


end Finite


end M4aHerbrand.Bridge
