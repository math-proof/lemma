import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.PullbackCanonical
open PullbackCanonical
open scoped nonZeroDivisors


namespace PullbackCanonical

/--
[pullbackDivisor_coeIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean)
-/
@[path]
lemma pullbackDivisor_coeIdeal
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [Module.IsTorsionFree R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  {I : Ideal R} :
-- imply
  pullbackDivisor R S K L (I : FractionalIdeal R⁰ K) = (I.map (algebraMap R S) : FractionalIdeal S⁰ L) :=
-- proof
  FractionalIdeal.extendedHomₐ_coeIdeal_eq_map L S I

end PullbackCanonical

namespace PullbackCanonical

/--
[pullbackDivisor_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean)
-/
@[path]
lemma pullbackDivisor_mul
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [Module.IsTorsionFree R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L]
  {I J : FractionalIdeal R⁰ K} :
-- imply
  pullbackDivisor R S K L (I * J) = pullbackDivisor R S K L I * pullbackDivisor R S K L J :=
-- proof
  map_mul (pullbackDivisor R S K L) I J

end PullbackCanonical

namespace PullbackCanonical

/--
[pullbackDivisor_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean)
-/
@[path]
lemma pullbackDivisor_one
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [Module.IsTorsionFree R S]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {L : Type*}
  [Field L]
  [Algebra S L]
  [IsFractionRing S L] :
-- imply
  pullbackDivisor R S K L (1 : FractionalIdeal R⁰ K) = 1 :=
-- proof
  map_one (pullbackDivisor R S K L)

end PullbackCanonical

namespace PullbackCanonical

/--
[absNorm_pullbackIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean)
-/
@[path]
lemma absNorm_pullbackIdeal
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [IsIntegrallyClosed R]
  [IsIntegrallyClosed S]
  [Algebra R S]
  [Module.Finite R S]
  [Module.IsTorsionFree R S]
  [Module.Free ℤ R]
  [Module.Free ℤ S]
  [Module.Finite ℤ S]
  [Module.Finite ℤ R]
  {I : Ideal R} :
-- imply
  Ideal.absNorm (I.map (algebraMap R S)) = (Ideal.absNorm I) ^ extensionDegree R S := by
-- proof
  unfold extensionDegree
  exact Ideal.absNorm_algebraMap R S I

end PullbackCanonical

namespace PullbackCanonical

/--
[degPullback_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean)
-/
@[path]
lemma degPullback_canonical
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [IsIntegrallyClosed R]
  [IsIntegrallyClosed S]
  [Algebra R S]
  [Module.Finite R S]
  [Module.IsTorsionFree R S]
  [Module.Free ℤ R]
  [Module.Free ℤ S]
  [Module.Finite ℤ S]
  [Module.Finite ℤ R]
  {K_Y : Ideal R} :
-- imply
  Ideal.absNorm (K_Y.map (algebraMap R S)) = (Ideal.absNorm K_Y) ^ extensionDegree R S :=
-- proof
  absNorm_pullbackIdeal R S K_Y

end PullbackCanonical


-- created on 2026-10-23
