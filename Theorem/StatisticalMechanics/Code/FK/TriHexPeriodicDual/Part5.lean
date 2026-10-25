/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem hexagonalIndexedEdge_mem (a : TriHexEdgeIndex) :
    hexagonalIndexedEdge a ∈ hexagonalGraph.edgeSet := by
  change hexagonalGraph.Adj (a.1, false) (a.1 + hexagonalStep a.2, true)
  exact hexagonal_adj_neighbor (a.1, false) a.2

end PeriodicPlanar
end FK
end StatMech
