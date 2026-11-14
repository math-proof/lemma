import Mathlib
import Def.IsDedekindDomain_FiniteUnitIdeles

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


variable {R K} in
theorem mem_unitIdeles_iff (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdeles R K ↔
      (∀ v : HeightOneSpectrum R, (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v : HeightOneSpectrum R,
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

end IsDedekindDomain.FiniteAdeleRing
