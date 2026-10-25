/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part9
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def hexagonalPairOrbitEquiv :
    Sym2 HexVertex ≃ Site 2 × HexagonalPairShape where
  toFun := hexagonalPairOrbitTo
  invFun := hexagonalPairOrbitFrom
  left_inv := hexagonalPairOrbitFrom_to
  right_inv := hexagonalPairOrbitTo_from

end StatMech.FK.PeriodicPlanar
