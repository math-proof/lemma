/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part7
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def hexagonalStraightEdgeArc {u v : HexVertex}
    (_huv : hexagonalGraph.Adj u v) :
    Path (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) :=
  Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v)

end StatMech.FK.PeriodicPlanar
