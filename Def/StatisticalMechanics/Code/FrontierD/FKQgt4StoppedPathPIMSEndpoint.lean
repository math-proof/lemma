/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4StoppedPathPIMSEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4PIMSTwoByOnePhaseAssembly
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHardCrossingOrientationNoGo.Part2
open Filter


namespace StatMech.FrontierD

open StatMech.FK StatMech.BeffaraDC

noncomputable section

def FKQgt4EvenTwoByOneStoppedPathPIMS (q : Real) : Prop :=
  forall scale k : Nat,
    0 < scale -> Even scale ->
    12 * scale + 2 < 2 * (k + 3) ->
    ∀ᶠ blocks in atTop,
      fkRectCriticalEventMass
            (fkRectWindingBlockVerticalFamily k scale blocks) q
            (fkRectDevelopedSquareHorizontalCrossingEvent
              (fkRectWindingBlockVerticalFamily k scale blocks) scale) ^ 6 /
          (16 * (1 + q ^ 2)) <=
        fkRectCriticalEventMass
          (fkRectWindingBlockVerticalFamily k scale blocks) q
          (fkRectDevelopedRectangleHorizontalCrossingEvent
            (fkRectWindingBlockVerticalFamily k scale blocks) scale
            0 (2 * (scale : Int)) 0 scale)


end
end StatMech.FrontierD
