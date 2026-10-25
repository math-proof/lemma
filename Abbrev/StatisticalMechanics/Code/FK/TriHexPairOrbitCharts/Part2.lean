/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Instance.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part3
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


abbrev HexagonalPairShape :=
  ({d : Site 2 // siteLexPositive d} × Bool × Bool) ⊕
    {bc : Bool × Bool // boolOrdered bc.1 bc.2}

end StatMech.FK.PeriodicPlanar
