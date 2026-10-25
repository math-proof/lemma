/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Sequences
import Def.v1.Atlas.LieGroups.code.ContinuousRep


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

structure IsInvariantSubspace (π : ContinuousRep G V)
    (W : Submodule ℂ V) : Prop where
  isClosed : IsClosed (W : Set V)
  invariant : ∀ (g : G) (v : V), v ∈ W → (π.toMonoidHom g) v ∈ W

end ContinuousRep
end
