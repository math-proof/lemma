/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConditions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part9
open scoped BigOperators


set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def numClusters (bc : BoundaryCondition) (ω : Sym2 V → Bool) : ℕ :=
  match bc with
  | BoundaryCondition.free => numClustersFree G ω
  | BoundaryCondition.wired => numClustersWired G bdry ω
  | BoundaryCondition.periodic => numClustersFree G ω

end Lattice
end StatMech
