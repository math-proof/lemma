/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/AdicValuation.lean -/


import Mathlib.NumberTheory.FunctionField
import Theorem.RingTheory.DedekindDomain.AdicValuation
import Lemma.Int.DedekindDomain.AdicValuation
open IsDedekindDomain


namespace MathlibExtTest.RingTheory.DedekindDomain.AdicValuation

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

example (v : HeightOneSpectrum R) :
    (v.valuationSubringAtPrime K).toSubring =
      (v.adicCompletionIntegers K).toSubring.comap (algebraMap K (v.adicCompletion K)) :=
  v.valuationSubringAtPrime_eq_comap_adicCompletionIntegers

variable {F L : Type*} [Field F] [Field L] [Algebra (Polynomial F) L]
  [Algebra (RatFunc F) L] [IsScalarTower (Polynomial F) (RatFunc F) L]
  [FunctionField F L] [Algebra.IsSeparable (RatFunc F) L]

example (v : HeightOneSpectrum (FunctionField.ringOfIntegers F L)) :
    (v.valuationSubringAtPrime L).toSubring =
      (v.adicCompletionIntegers L).toSubring.comap (algebraMap L (v.adicCompletion L)) :=
  v.valuationSubringAtPrime_eq_comap_adicCompletionIntegers

end MathlibExtTest.RingTheory.DedekindDomain.AdicValuation
