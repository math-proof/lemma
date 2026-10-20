import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.FractionalIdeal.Spectrum
open scoped nonZeroDivisors Pointwise
open PrimeSpectrum


/--
[smul_asIdeal_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Spectrum.lean)
-/
@[path]
private lemma smul_asIdeal_coe_eq
  [Group G] [CommRing R] [IsDomain R] [CommRing K] [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]
  {g : G}
  {p : PrimeSpectrum R} :
-- imply
  FractionalIdeal.coeIdeal (S := by
-- proof
  apply PrimeSpectrum.smul_asIdeal_coe g p


-- created on 2026-10-20
