/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingRankOneReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberBalance
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseTail.Part2


namespace StatMech.FrontierD

noncomputable section

def FKRectRankOnePositiveVerticalBoundaryCutFiberBound
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ K : (fkRectOpenGraph R omega).ConnectedComponent,
    ¬ FKRectPrimalComponentHasNet R omega K →
      fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤
        fkRectPrimalComponentHorizontalCutCrossingCount R omega K


end
end StatMech.FrontierD
