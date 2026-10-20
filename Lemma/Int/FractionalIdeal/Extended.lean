import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.FractionalIdeal.Extended
open nonZeroDivisors
open FractionalIdeal


/--
[extendedHom_div_of_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Extended.lean)
-/
@[path]
private lemma extendedHom_div_of_fg_eq
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Algebra A B] [Module.IsTorsionFree A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K]
  {S : Submonoid A} [IsLocalization S B]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ0 : J ≠ 0)
  (hJ : (J : Submodule A K).FG) :
-- imply
  extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J := by
-- proof
  apply FractionalIdeal.extendedHom_div_of_fg S I J hJ0 hJ

/--
[extendedHom_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/Extended.lean)
-/
@[path]
private lemma extendedHom_div_eq
  [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Algebra A B] [Module.IsTorsionFree A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K] [IsNoetherianRing A]
  {S : Submonoid A} [IsLocalization S B]
  {I J : FractionalIdeal A⁰ K}
-- given
  (hJ : J ≠ 0) :
-- imply
  extendedHom K B (I / J) = extendedHom K B I / extendedHom K B J := by
-- proof
  apply FractionalIdeal.extendedHom_div S I J hJ


-- created on 2026-10-20
