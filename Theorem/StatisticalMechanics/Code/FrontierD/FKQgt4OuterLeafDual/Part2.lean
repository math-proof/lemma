/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part3
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section

@[simp] theorem pfdOuterLeafCollapse_endpoint (P : PlanarZ2Subgraph)
    (e : kwg_Edge P) (side : Bool) :
    pfdOuterLeafCollapse P (pfdOuterLeafEndpoint P e side) =
      pfdOuterLeafSideFace P e side := by
  unfold pfdOuterLeafEndpoint
  split
  · simpa [pfdOuterLeafCollapse] using ‹pfdOuterLeafSideFace P e side = pfdOuterFace P›.symm
  · rfl


end
end StatMech.FrontierD
