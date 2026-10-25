/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


def triHexLiftEntry (i : Fin 3) : Fin 3 :=
  ![2, 2, 1] i


def triHexLiftExit (i : Fin 3) : Fin 3 :=
  ![1, 0, 0] i

end PeriodicPlanar
end FK
end StatMech
