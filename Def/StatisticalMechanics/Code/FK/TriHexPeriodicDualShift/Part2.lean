/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def hexagonalEdgeTranslate (z : Site 2)
    (e : hexagonalGraph.edgeSet) : hexagonalGraph.edgeSet :=
  let a := hexagonalEdgeChartEquiv.symm e
  hexagonalEdgeChart (a.1 + z, a.2)

end StatMech.FK.PeriodicPlanar
