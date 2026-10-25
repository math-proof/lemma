/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part3
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularPairOrbitFrom
    (a : Site 2 × TriangularPairShape) : Sym2 (Site 2) :=
  s(a.1, a.1 + a.2.1)

end StatMech.FK.PeriodicPlanar
