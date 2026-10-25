/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls

noncomputable section

def kwg_pathEdgeIndex (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) : {edge // edge ∈ path.edges} -> kwg_Edge P :=
  fun edge => ⟨edge.1, path.edges_subset_edgeSet edge.2⟩


def kwg_pathEdgeIndices (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) : List (kwg_Edge P) :=
  path.edges.attach.map (kwg_pathEdgeIndex P path)

end
end StatMech.Onsager
