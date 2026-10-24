/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DirectLimitSections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Filtered.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NoetherianColimit

open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace

noncomputable section

universe u w

namespace TopCat.Sheaf

variable {C : Type (u+1)} [Category.{u} C]
         {J : Type w} [SmallCategory J]
         {X : TopCat.{u}}

/-- If the target category `C` has `J`-shaped colimits and weak sheafification, then the
category of `C`-valued sheaves on `X` also has `J`-shaped colimits. -/
instance hasColimitsOfShape_of_hasWeakSheafify
    [HasColimitsOfShape J C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasColimitsOfShape J (TopCat.Sheaf C X) :=
  inferInstanceAs (HasColimitsOfShape J
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) C))

end TopCat.Sheaf

/-- On a Noetherian space, a filtered colimit of sheaves, computed at the level of presheaves,
is again a sheaf (the key sheaf-theoretic content of Lemma 22). -/
theorem noetherian_filtered_colimit_presheaf_isSheaf
    {C : Type (u+1)} [Category.{u} C]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {X : TopCat.{u}} [NoetherianSpace X]
    [HasColimitsOfShape J C]
    (F : J ⥤ TopCat.Sheaf C X)
    (c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) C))
    (hc : IsColimit c) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) c.pt :=
  TopCat.Sheaf.filteredColimitPresheafIsSheaf F c hc

/-- Lemma 22 (Noetherian): On a Noetherian space, sections of a filtered colimit of sheaves
on an open `U` are computed as the filtered colimit of sections on `U`. -/
def noetherian_filtered_colimit_sheaf_sections_iso
    {C : Type (u+1)} [Category.{u} C]
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {X : TopCat.{u}} [NoetherianSpace X]
    [HasColimitsOfShape J C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : J ⥤ TopCat.Sheaf C X)
    (U : Opens X) :
    ((Sheaf.forget C X).obj (colimit F)).obj (op U) ≅
      colimit (F ⋙ Sheaf.forget C X ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op U)) := by
  haveI : CreatesColimit F (sheafToPresheaf (Opens.grothendieckTopology X) C) :=
    Sheaf.createsColimitOfIsSheaf F
      (fun c hc => noetherian_filtered_colimit_presheaf_isSheaf F c hc)
  have hp : PreservesColimit F (sheafToPresheaf (Opens.grothendieckTopology X) C) :=
    preservesColimit_of_createsColimit_and_hasColimit F
      (sheafToPresheaf (Opens.grothendieckTopology X) C)
  exact (@preservesColimitIso _ _ _ _
    (sheafToPresheaf (Opens.grothendieckTopology X) C) _ _ F hp inferInstance).app (op U) ≪≫
    colimitObjIsoColimitCompEvaluation
      (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) C) (op U)
