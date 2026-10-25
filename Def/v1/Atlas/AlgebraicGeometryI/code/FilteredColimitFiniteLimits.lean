/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitFiniteLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic
open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v u₁ u₂ u

variable {C : Type u} [Category.{v} C]
variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]


/-- Filtered colimits commute with finite limits: the canonical comparison
`colim_K lim_J F ≅ lim_J colim_K F` is an isomorphism under the hypothesis that
the colimit functor preserves finite limits. -/
noncomputable def filteredColimit_finiteLimits_iso
    [HasLimitsOfShape J C] [HasColimitsOfShape K C]
    [PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _)]
    (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  colimitLimitIso F

