/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part2
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


def hexToTriAnchor (u : HexVertex) : Site 2 :=
  if u.2 then u.1 - hexagonalStep 0 else u.1


end PeriodicPlanar
end FK
end StatMech
