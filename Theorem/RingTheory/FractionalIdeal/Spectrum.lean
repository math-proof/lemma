/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Spectrum.lean -/
module

public import Abbrev.RingTheory.FractionalIdeal.GroupAction
public import Theorem.Int.FractionalIdeal.GroupAction
public import Theorem.Int.Spectrum.Prime.GroupAction
open scoped nonZeroDivisors Pointwise

/-!
# Compatibility of fractional-ideal and prime-spectrum actions
-/

public section


namespace PrimeSpectrum

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing K]
  [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]
end PrimeSpectrum
