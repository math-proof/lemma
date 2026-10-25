/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part10
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularEdgePairShape (i : Fin 3) : TriangularPairShape :=
  (triangularPairNormal 0 (triangularStep i)).2


def triangularEdgePairBase (i : Fin 3) : Site 2 :=
  (triangularPairNormal 0 (triangularStep i)).1


def hexagonalEdgePairShape (i : Fin 3) : HexagonalPairShape :=
  (hexagonalPairNormal (0, false) (hexagonalStep i, true)).2

end StatMech.FK.PeriodicPlanar
