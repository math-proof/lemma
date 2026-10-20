/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Spectrum.lean -/

import sympy.atlas.RingTheory.FractionalIdeal.GroupAction
import sympy.atlas.RingTheory.Spectrum.Prime.GroupAction
/-!
# Compatibility of fractional-ideal and prime-spectrum actions
-/

open scoped nonZeroDivisors Pointwise

namespace PrimeSpectrum

variable {G R K : Type*} [Group G] [CommRing R] [IsDomain R] [CommRing K]
  [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]

/-- The prime-spectrum action is the restriction of the fractional-ideal action. -/
@[simp]
theorem smul_asIdeal_coe (g : G) (p : PrimeSpectrum R) :
    FractionalIdeal.coeIdeal (S := R⁰) (P := K) (g • p).asIdeal =
      g • FractionalIdeal.coeIdeal (S := R⁰) (P := K) p.asIdeal := by
  rw [smul_asIdeal, FractionalIdeal.smul_coeIdeal]

end PrimeSpectrum
