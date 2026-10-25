/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitFiniteLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]


/-- In the category of types, filtered colimits preserve finite limits. -/
noncomputable instance filteredColimit_preservesFiniteLimits_type
    [Small.{v, u₂} K] [IsFiltered K] :
    PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) :=
  filtered_colim_preservesFiniteLimits_of_types

