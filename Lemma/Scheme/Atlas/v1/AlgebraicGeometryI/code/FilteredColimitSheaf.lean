import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.NoetherianColimit
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


/--
[lemma22_filtered_colimit_sheaf_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitSheaf.lean)
-/
@[path]
lemma lemma22_filtered_colimit_sheaf_noetherian
  {C : Type u}
  [Category.{v} C]
  {X : TopCat.{w}}
  {J : Type t}
  [Category.{t} J]
  [IsFiltered J]
  [NoetherianSpace X]
  [HasColimitsOfShape J C]
  {F : J ⥤ TopCat.Sheaf C X}
  {c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C)}
-- given
  (hc : IsColimit c) :
-- imply
  TopCat.Presheaf.IsSheaf c.pt :=
-- proof
  TopCat.Sheaf.filteredColimitPresheafIsSheaf F c hc


-- created on 2026-10-23
