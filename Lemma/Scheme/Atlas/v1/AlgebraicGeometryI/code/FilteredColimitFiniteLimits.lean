import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
open CategoryTheory CategoryTheory.Limits


/--
[filteredColimit_finiteLimits_iso_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitFiniteLimits.lean)
-/
@[path]
lemma filteredColimit_finiteLimits_iso_components
  {C : Type u}
  [Category.{v} C]
  {J : Type u₁}
  [Category.{v₁} J]
  {K : Type u₂}
  [Category.{v₂} K]
  [HasLimitsOfShape J C]
  [HasColimitsOfShape K C]
  [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]
  {F : J ⥤ K ⥤ C}
  {a : K}
  {b : J} :
-- imply
  colimit.ι (limit F) a ≫ (filteredColimit_finiteLimits_iso F).hom ≫ limit.π (colimit F.flip) b = (limit.π F b).app a ≫ (colimit.ι F.flip a).app b :=
-- proof
  ι_colimitLimitIso_limit_π F a b


-- created on 2026-10-23
