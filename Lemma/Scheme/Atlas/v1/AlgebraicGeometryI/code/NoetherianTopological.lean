import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.NoetherianTopological
open TopologicalSpace Set NoetherianTopological


namespace NoetherianTopological

/--
[primeSpectrum_noetherianSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianTopological.lean)
-/
@[path]
lemma primeSpectrum_noetherianSpace
  {R : Type u}
  [CommSemiring R]
  [IsNoetherianRing R] :
-- imply
  NoetherianSpace (PrimeSpectrum R) :=
-- proof
  inferInstance

end NoetherianTopological

namespace NoetherianTopological

/--
[noetherian_finite_minimalPrimes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianTopological.lean)
-/
@[path]
lemma noetherian_finite_minimalPrimes
  {R : Type u}
  [CommSemiring R]
  [IsNoetherianRing R] :
-- imply
  (minimalPrimes R).Finite :=
-- proof
  minimalPrimes.finite_of_isNoetherianRing R

end NoetherianTopological

namespace NoetherianTopological

/--
[sInf_minimalPrimes_eq_nilradical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianTopological.lean)
-/
@[path]
lemma sInf_minimalPrimes_eq_nilradical
  {R : Type*}
  [CommSemiring R] :
-- imply
  sInf (minimalPrimes R) = nilradical R := by
-- proof
  show sInf (Ideal.minimalPrimes ⊥) = nilradical R
  rw [Ideal.sInf_minimalPrimes]
  rfl

end NoetherianTopological

namespace NoetherianTopological

/--
[reduced_sInf_minimalPrimes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianTopological.lean)
-/
@[path]
lemma reduced_sInf_minimalPrimes
  {R : Type*}
  [CommSemiring R]
  [IsReduced R] :
-- imply
  sInf (minimalPrimes R) = (⊥ : Ideal R) := by
-- proof
  rw [sInf_minimalPrimes_eq_nilradical]
  exact nilradical_eq_zero R

end NoetherianTopological


-- created on 2026-10-23
