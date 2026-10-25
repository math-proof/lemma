/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Theorem.v1.Atlas.LieGroups.code.KFinite


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
