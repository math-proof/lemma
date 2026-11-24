module
public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.Complex.IsStronglyContinuousToMonoidHom
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.v1.Atlas.LieGroups.code.KFinite.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

theorem mem_kFiniteSubspace (π : ContinuousRep G V) (K : Subgroup G)
    (v : V) : v ∈ kFiniteSubspace π K ↔ IsKFinite π K v :=
  Iff.rfl

end ContinuousRep
end
