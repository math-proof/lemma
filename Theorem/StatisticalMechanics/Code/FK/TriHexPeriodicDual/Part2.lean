/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDual
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem triangularIndexedEdge_mem (a : TriHexEdgeIndex) :
    triangularIndexedEdge a ∈ triangularGraph.edgeSet := by
  change triangularGraph.Adj a.1 (a.1 + triangularStep a.2)
  exact triangular_adj_neighbor a.1 (a.2, true)

end PeriodicPlanar
end FK
end StatMech
