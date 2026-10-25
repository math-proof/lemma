/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part3
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def triangularStraightEdgeArc {x y : Site 2}
    (_hxy : triangularGraph.Adj x y) :
    Path (triangularPlaneVertex x) (triangularPlaneVertex y) :=
  Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y)

end StatMech.FK.PeriodicPlanar
