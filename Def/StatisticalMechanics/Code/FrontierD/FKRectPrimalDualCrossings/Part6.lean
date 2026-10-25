/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectPrimalDualCrossingRepresentativeSourceIndex
    (R : FKRectTorus) (eta : R.Configuration) :
    ({C : (fkRectOpenGraph R
          (fkRectForceCutClosed R eta)).ConnectedComponent //
        FKRectRawHorizontalCrossingComponent R
          (fkRectForceCutClosed R eta) C} ⊕
      {C : (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta))).ConnectedComponent //
        FKRectRawHorizontalCrossingComponent R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) C}) →
      Fin (2 * R.height)
  | Sum.inl C => fkRectPrimalDualCrossingSourceIndexEquiv R
      (Sum.inl (fkRectRawHorizontalCrossingRepresentative R
        (fkRectForceCutClosed R eta) C))
  | Sum.inr C => fkRectPrimalDualCrossingSourceIndexEquiv R
      (Sum.inr (fkRectRawHorizontalCrossingRepresentative R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) C))

end
end StatMech.FrontierD
