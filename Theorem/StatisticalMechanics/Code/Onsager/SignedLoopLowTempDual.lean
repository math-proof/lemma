/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

@[simp] theorem kwg_pathEdgeIndices_map_val
    (P : PlanarZ2Subgraph) {u v : P.V} (path : P.G.Walk u v) :
    (kwg_pathEdgeIndices P path).map Subtype.val = path.edges := by
  simp [kwg_pathEdgeIndices, kwg_pathEdgeIndex]


end
end StatMech.Onsager
