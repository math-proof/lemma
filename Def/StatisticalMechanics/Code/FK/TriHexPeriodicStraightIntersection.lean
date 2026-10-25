/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicStraightIntersection
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

def hexagonalScaledCoordinate (u : HexVertex) (k : Fin 2) : Int :=
  3 * u.1 k + if u.2 then -1 else 1

end StatMech.FK.PeriodicPlanar
