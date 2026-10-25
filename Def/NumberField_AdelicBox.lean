import Instance.NumberField_AdelicHaar

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicBox

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

variable (v : HeightOneSpectrum R)


end Finite

section Infinite

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in

def infiniteBox : Set (InfiniteAdeleRing K) :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K ⁻¹'
    ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

end Infinite

section Box

variable (K : Type*) [Field K] [NumberField K]

def adelicBox : Set (AdeleRing (𝓞 K) K) :=
  {x | x.1 ∈ infiniteBox K ∧ x.2 ∈ integralFiniteAdeles (𝓞 K) K}


end Box

end NumberField.AdelicBox

end
