/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part9
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem hexagonalPairOrbitTo_mk (u v : HexVertex) :
    hexagonalPairOrbitTo s(u, v) = hexagonalPairNormal u v := by
  exact Sym2.lift_mk _ _ _


end StatMech.FK.PeriodicPlanar
