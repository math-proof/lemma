/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3


namespace StatMech.FrontierD

noncomputable section

def FKRectZeroTurnReachablePrimalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) : Prop :=
  X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C ∧
    (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))


end
end StatMech.FrontierD
