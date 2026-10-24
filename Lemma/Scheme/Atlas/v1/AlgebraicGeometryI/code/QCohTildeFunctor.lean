import Mathlib
import sympy.Basic
open Submodule


namespace QCohTildeFunctor

/--
[element_zero_of_localization_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohTildeFunctor.lean)
-/
@[path]
lemma element_zero_of_localization_zero
  [CommRing R]
  [AddCommGroup N]
  [Module R N]
  {n : N}
-- given
  (h : ∀ (P : Ideal R) [P.IsMaximal], LocalizedModule.mkLinearMap P.primeCompl N n = 0) :
-- imply
  n = 0 :=
-- proof
  @Module.eq_of_localization_maximal R N _ _ _
    (fun P _ => LocalizedModule P.primeCompl N)
    (fun P _ => inferInstance) (fun P _ => inferInstance)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl N)
    (fun P _ => inferInstance)
    n 0 (fun P _ => by rw [h P, map_zero])

end QCohTildeFunctor

namespace QCohTildeFunctor

/--
[localization_localization_isLocalization'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohTildeFunctor.lean)
-/
@[path]
lemma localization_localization_isLocalization'
  [CommRing R]
  {M : Submonoid R}
  [CommRing S]
  [Algebra R S]
  [IsLocalization M S]
  {N : Submonoid S}
  {T : Type*}
  [CommRing T]
  [Algebra R T]
  [Algebra S T]
  [IsScalarTower R S T]
  [IsLocalization N T] :
-- imply
  IsLocalization (IsLocalization.localizationLocalizationSubmodule M N) T :=
-- proof
  IsLocalization.localization_localization_isLocalization M N T

end QCohTildeFunctor


-- created on 2026-10-23
