/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitSheafAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NoetherianCoverFinite
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w v u t

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}
variable {J : Type t} [Category.{t} J] [IsFiltered J]

/-- Lem 22, Lec 12: on a Noetherian space, a filtered colimit of sheaves is
already a sheaf; equivalently, the underlying presheaf colimit satisfies the
sheaf condition because finite covers and filtered colimits commute. -/
end TopCat.Sheaf
