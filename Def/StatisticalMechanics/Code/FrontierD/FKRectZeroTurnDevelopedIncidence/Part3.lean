/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectPrimalDevelopedExtremeSameSign
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
    ∀ (C : FKRectZeroTurnCutRemainderComponent R omega)
      (X : FKRectRawPrimalHorizontalCrossingComponent R omega),
      X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
      ¬ (fkRectOpenGraph R omega).Reachable
        (fkRectMedialWestPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C)))
        (fkRectMedialEastPrimal R
          (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
            (fkRectZeroTurnRemainderSide R omega C))) →
      let d := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
        (fkRectZeroTurnRemainderSide R omega C)
      let e := fkRectZeroTurnRemainderOrientedDart R omega C
        (fkMedialCheckerColor d)
      0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).1


end
end StatMech.FrontierD
