import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.RamificationFiltration
open IsLocalRing
open IsDiscreteValuationRing


/--
[map_maximalIdeal_eq_pow_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/RamificationFiltration.lean)
-/
@[path]
private lemma map_maximalIdeal_eq_pow_ramificationIdx_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)] :
-- imply
  Ideal.map (algebraMap A B) (maximalIdeal A) =
    maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by
-- proof
  apply IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx

/--
[algebraMap_mem_maximalIdeal_pow_ramificationIdx](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/RamificationFiltration.lean)
-/
@[path]
private lemma algebraMap_mem_maximalIdeal_pow_ramificationIdx_eq
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
  {x : A}
-- given
  (hx : x ∈ maximalIdeal A) :
-- imply
  algebraMap A B x ∈ maximalIdeal B ^ (maximalIdeal B).ramificationIdx A := by
-- proof
  apply IsDiscreteValuationRing.algebraMap_mem_maximalIdeal_pow_ramificationIdx hx


-- created on 2026-10-20
