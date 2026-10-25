/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnUsesAdaptiveDualRoute_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C ↔
      ∀ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
        X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
        ¬ (fkRectOpenGraph R omega).Reachable
          (fkRectMedialWestPrimal R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
              (fkRectZeroTurnRemainderSide R omega C)))
          (fkRectMedialEastPrimal R
            (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
              (fkRectZeroTurnRemainderSide R omega C))) := by
  constructor
  · intro h X hX hreach
    exact h ⟨X, hX, hreach⟩
  · rintro h ⟨X, hX, hreach⟩
    exact h X hX hreach


end
end StatMech.FrontierD
