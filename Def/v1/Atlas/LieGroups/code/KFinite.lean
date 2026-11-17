/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def IsKFinite (π : ContinuousRep G V) (K : Subgroup G) (v : V) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) : Submodule ℂ V)

end ContinuousRep
end
