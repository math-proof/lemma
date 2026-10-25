/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part8
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


@[simp]
theorem numClusters_free (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.free ω = numClustersFree G ω := rfl

@[simp]
theorem numClusters_wired (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.wired ω = numClustersWired G bdry ω := rfl

@[simp]
theorem numClusters_periodic (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.periodic ω = numClustersFree G ω := rfl


theorem numClusters_wired_le_free (ω : Sym2 V → Bool) :
    numClusters G bdry BoundaryCondition.wired ω
      ≤ numClusters G bdry BoundaryCondition.free ω :=
  numClustersWired_le_numClustersFree G bdry ω

end Lattice
end StatMech
