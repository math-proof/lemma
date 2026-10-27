import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.DirectLimitSections
open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace


/--
[noetherian_filtered_colimit_presheaf_isSheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DirectLimitSections.lean)
-/
@[path]
private lemma noetherian_filtered_colimit_presheaf_isSheaf_eq
  {C : Type (u+1)}
  [Category.{u} C]
  {J : Type w}
  [SmallCategory J]
  [IsFiltered J]
  {X : TopCat.{u}}
  [NoetherianSpace X]
  [HasColimitsOfShape J C]
  {F : J ⥤ TopCat.Sheaf C X}
  {c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) C)}
-- given
  (hc : IsColimit c) :
-- imply
  CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) c.pt := by
-- proof
  apply noetherian_filtered_colimit_presheaf_isSheaf F c hc


-- created on 2026-10-23
