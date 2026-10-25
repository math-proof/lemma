/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part8
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def hexagonalPairOrbitFrom
    (a : Site 2 × HexagonalPairShape) : Sym2 HexVertex :=
  match a.2 with
  | Sum.inl s => s((a.1, s.2.1), (a.1 + s.1.1, s.2.2))
  | Sum.inr s => s((a.1, s.1.1), (a.1, s.1.2))

end StatMech.FK.PeriodicPlanar
