import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.FractionalIdeal.Spectrum
open scoped nonZeroDivisors Pointwise
open PrimeSpectrum


namespace PrimeSpectrum

/--
[smul_asIdeal_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Spectrum.lean)
-/
@[path]
lemma smul_asIdeal_coe
  [Group G] [CommRing R] [IsDomain R] [CommRing K] [MulSemiringAction G R] [Algebra R K] [IsFractionRing R K]
  {g : G}
  {p : PrimeSpectrum R} :
-- imply
  FractionalIdeal.coeIdeal (S := by
-- proof
  rw [smul_asIdeal, FractionalIdeal.smul_coeIdeal]

end PrimeSpectrum


-- created on 2026-10-20
-- updated on 2026-10-26
