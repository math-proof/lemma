import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.AdicCompletionIntegers
open IsDedekindDomain.HeightOneSpectrum


/--
[map_asIdeal_eq_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/AdicCompletionIntegers.lean)
-/
@[path]
private lemma map_asIdeal_eq_maximalIdeal_eq
  [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {v : HeightOneSpectrum A} :
-- imply
  Ideal.map (algebraMap A ↥(v.adicCompletionIntegers K)) v.asIdeal =
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K) := by
-- proof
  apply IsDedekindDomain.HeightOneSpectrum.map_asIdeal_eq_maximalIdeal v


-- created on 2026-10-20
