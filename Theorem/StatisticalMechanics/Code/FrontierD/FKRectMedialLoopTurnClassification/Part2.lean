/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialLoopTurnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

open FKMedialTurningFiber

noncomputable section

variable {T : EvenTorus}

theorem fkRectBlackBoundaryPointAfter_succ
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (n : Nat) :
    fkRectBlackBoundaryPointAfter R pairing d (n + 1) =
      ((fkRectBlackBoundaryPointAfter R pairing d n).1 +
          2 * ons_dirExponentX
            (fkMedialStrandDirection pairing
              ((fkMedialBlackBoundaryPerm pairing)^[n] d).1),
        (fkRectBlackBoundaryPointAfter R pairing d n).2 +
          2 * ons_dirExponentY
            (fkMedialStrandDirection pairing
              ((fkMedialBlackBoundaryPerm pairing)^[n] d).1)) := by
  unfold fkRectBlackBoundaryPointAfter
  rw [fkRectRefinedBoundaryCenterAfter_succ_right]
  rw [fkMedialBlackBoundaryPerm_iterate_val pairing d n,
    fkMedialBlackBoundaryPerm_iterate_val pairing d (n + 1)]
  rw [Function.iterate_succ_apply']
  exact fkRectRefinedBoundaryStep_point pairing
    ((fkMedialBoundaryStep pairing)^[n] d.1)
    (fkRectRefinedBoundaryCenterAfter pairing d.1
      (fkRectRefinedBoundaryCanonicalCenter R d.1) n)

end
end StatMech.FrontierD
