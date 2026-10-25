/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem card_fkRectPrimalDualCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) :
    Fintype.card
        {i : Fin (2 * R.height) //
          FKRectPrimalDualCrossingSource R eta i} =
      fkRectRawHorizontalCrossingSourceCount R
          (fkRectForceCutClosed R eta) +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) := by
  rw [Fintype.card_congr
    (fkRectPrimalDualCrossingSourceSubtypeEquiv R eta),
    Fintype.card_sum,
    card_fkRectRawHorizontalCrossingSource,
    card_fkRectRawHorizontalCrossingSource]

theorem fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawPrimalDualHorizontalCrossingClusterCount R eta <=
      fkRectRawHorizontalCrossingSourceCount R eta +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R eta) := by
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount
  exact Nat.add_le_add
    (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R eta)
    (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R
      (fkRectDualConfigurationEquiv R eta))

theorem fkRectPrimalDualHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R eta <=
      fkRectRawHorizontalCrossingSourceCount R
          (fkRectForceCutClosed R eta) +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) := by
  unfold fkRectPrimalDualHorizontalCrossingClusterCount
  exact
    fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount R _


end
end StatMech.FrontierD
