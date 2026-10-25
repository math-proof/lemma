/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

def hexagonalEdgeChart (a : TriHexEdgeIndex) : hexagonalGraph.edgeSet :=
  ⟨hexagonalIndexedEdge a, hexagonalIndexedEdge_mem a⟩

end PeriodicPlanar
end FK
end StatMech
