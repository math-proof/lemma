/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Theorem.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part5
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


def siteLexPositive (d : Site 2) : Prop :=
  0 < d 0 ∨ d 0 = 0 ∧ 0 < d 1

end StatMech.FK.PeriodicPlanar
