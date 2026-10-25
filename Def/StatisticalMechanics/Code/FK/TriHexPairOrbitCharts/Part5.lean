/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part4
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularPairOrbitEquiv :
    Sym2 (Site 2) ≃ Site 2 × TriangularPairShape where
  toFun := triangularPairOrbitTo
  invFun := triangularPairOrbitFrom
  left_inv := triangularPairOrbitFrom_to
  right_inv := triangularPairOrbitTo_from

end StatMech.FK.PeriodicPlanar
