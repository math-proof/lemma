/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.Complex.IsStronglyContinuousToMonoidHom
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Theorem.v1.Atlas.LieGroups.code.KFinite

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def kFiniteSubspace (π : ContinuousRep G V) (K : Subgroup G) :
    Submodule ℂ V where
  carrier := {v : V | IsKFinite π K v}
  zero_mem' := isKFinite_zero π K
  add_mem' := fun {a b} ha hb => isKFinite_add π K a b ha hb
  smul_mem' := fun c {v} hv => isKFinite_smul π K c v hv

end ContinuousRep
end
