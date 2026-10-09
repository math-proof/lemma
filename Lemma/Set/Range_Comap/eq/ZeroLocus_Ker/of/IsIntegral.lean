import Mathlib
import sympy.Basic

open PrimeSpectrum

/--
[PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PrimeSpectrum_range_comap_eq_zeroLocus_ker_of_isIntegral.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {S : Type v} [CommRing S]
  {f : R →+* S}
-- given
  (hf : f.IsIntegral) :
-- imply
  Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.zeroLocus (RingHom.ker f) := by
-- proof
  rw [← (PrimeSpectrum.isClosedMap_comap_of_isIntegral f hf).isClosed_range.closure_eq,
    PrimeSpectrum.closure_range_comap]


-- created on 2026-10-05
