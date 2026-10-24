/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Spectrum.lean -/

import sympy.atlas.RingTheory.FractionalIdeal.GroupAction
import Lemma.Int.FractionalIdeal.GroupAction
import Lemma.Int.Spectrum.Prime.GroupAction
/-!
# Compatibility of fractional-ideal and prime-spectrum actions
-/

open scoped nonZeroDivisors Pointwise

namespace PrimeSpectrum

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing K]
  [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]
end PrimeSpectrum
