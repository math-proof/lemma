/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Instance.StatisticalMechanics.Code.BeffaraDC.TorusWindingThinObstruction
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

noncomputable def windingThinCounterexampleConfig : TorusAmbientConfig 8 :=
  fun e =>
    match (torusEdgeCodeEquiv 8).symm e with
    | ((x, y), TorusEdgeOrientation.horizontal) => decide (y = 0 ∨ x = y)
    | ((x, y), TorusEdgeOrientation.vertical) => decide (x = y + 1)

end StatMech.BeffaraDC
