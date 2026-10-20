import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.AdicValuation
open IsDedekindDomain.HeightOneSpectrum


/--
[valuationSubringAtPrime_eq_comap_adicCompletionIntegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicValuation.lean)
-/
@[path]
private lemma valuationSubringAtPrime_eq_comap_adicCompletionIntegers_eq
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} :
-- imply
  (valuationSubringAtPrime (K := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_comap_adicCompletionIntegers v


-- created on 2026-10-20
