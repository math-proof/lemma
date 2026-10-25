/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part5
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


noncomputable def hexagonalPlaneVertexValue (u : HexVertex) : Complex :=
  triHexPlanePeriod u.1 + hexagonalFaceCenterOffset u.2

end StatMech.FK.PeriodicPlanar
