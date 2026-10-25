import Mathlib
import sympy.Basic
import Theorem.RingTheory.DedekindDomain.AdicValuation
open IsDedekindDomain.HeightOneSpectrum


namespace IsDedekindDomain.HeightOneSpectrum

/--
[valuationSubringAtPrime_eq_comap_adicCompletionIntegers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicValuation.lean)
-/
@[path]
lemma valuationSubringAtPrime_eq_comap_adicCompletionIntegers
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} :
-- imply
  (valuationSubringAtPrime (K := by
-- proof
  ext x
  simp only [Subring.mem_comap, ValuationSubring.mem_toSubring]
  simp only [valuationSubringAtPrime_eq_valuationSubring, Valuation.mem_valuationSubring_iff]
  rw [mem_adicCompletionIntegers]
  change (valuation K v) x ≤ 1 ↔ Valued.v (x : adicCompletion K v) ≤ 1
  rw [valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum


-- created on 2026-10-20
-- updated on 2026-10-23
