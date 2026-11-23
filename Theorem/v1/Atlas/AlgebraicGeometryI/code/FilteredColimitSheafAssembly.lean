/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FilteredColimitSheafAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.NoetherianCoverFinite
public import Instance.v1.Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

public section

/-- Lem 22, Lec 12: on a Noetherian space, a filtered colimit of sheaves is
already a sheaf; equivalently, the underlying presheaf colimit satisfies the
sheaf condition because finite covers and filtered colimits commute. -/


namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}
variable {J : Type t} [Category.{t} J] [IsFiltered J]

end TopCat.Sheaf
noncomputable section

universe w v u t

end
