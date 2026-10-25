-- Carved from Lemma/Definitions/Def_Mathlib_RingTheory_DedekindDomain_AdicValuation.lean: instance decls only.
import Mathlib

section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    ⟨_, Set.countable_range _, denseRange_algebraMap (K := K) (v := v)⟩


end IsDedekindDomain.HeightOneSpectrum

end
