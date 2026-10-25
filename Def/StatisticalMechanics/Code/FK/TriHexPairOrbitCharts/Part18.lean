/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part15
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triHexPairShapeOffset (s : TriangularPairShape) : Site 2 :=
  if s = triangularEdgePairShape 2 then ![0, -1] else 0

end StatMech.FK.PeriodicPlanar
