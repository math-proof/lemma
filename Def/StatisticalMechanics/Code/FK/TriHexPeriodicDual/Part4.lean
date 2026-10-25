/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

def hexagonalIndexedEdge (a : TriHexEdgeIndex) : Sym2 HexVertex :=
  s((a.1, false), (a.1 + hexagonalStep a.2, true))

end PeriodicPlanar
end FK
end StatMech
