/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/FractionalIdeal/Spectrum.lean -/


import sympy.atlas.RingTheory.FractionalIdeal.Spectrum
import Lemma.Int.FractionalIdeal.Spectrum

/-!
# Tests for compatibility of fractional-ideal and prime-spectrum actions
-/


open scoped nonZeroDivisors Pointwise

namespace N150Test

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] (g : G) (p : PrimeSpectrum R) :
    FractionalIdeal.coeIdeal (S := R⁰) (P := K) (g • p).asIdeal =
      g • FractionalIdeal.coeIdeal (S := R⁰) (P := K) p.asIdeal :=
  PrimeSpectrum.smul_asIdeal_coe g p

end N150Test
