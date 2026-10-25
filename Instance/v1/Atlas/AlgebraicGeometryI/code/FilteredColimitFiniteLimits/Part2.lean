/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitFiniteLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits.Part2
open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]


/-- In a concrete category compatible with the forgetful functor, filtered
colimits commute with finite limits, generalizing the type-level statement. -/
noncomputable instance filteredColimit_preservesFiniteLimits_concrete
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [SmallCategory J] [FinCategory J]
    [Small.{v, u₂} K] [IsFiltered K]
    [HasLimitsOfShape J C] [HasColimitsOfShape K C]
    [ReflectsLimitsOfShape J (forget C)]
    [PreservesColimitsOfShape K (forget C)]
    [PreservesLimitsOfShape J (forget C)] :
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) :=
  filtered_colim_preservesFiniteLimits

