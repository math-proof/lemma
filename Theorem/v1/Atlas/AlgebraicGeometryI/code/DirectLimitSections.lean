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
import Def.v1.Atlas.AlgebraicGeometryI.code.NoetherianColimit
import Instance.v1.Atlas.AlgebraicGeometryI.code.DirectLimitSections
open CategoryTheory CategoryTheory.Limits TopCat Opposite TopologicalSpace


noncomputable section

universe u w

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

end
