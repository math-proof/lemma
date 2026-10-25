/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAllSectorVerticalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part41
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareVerticalRate
import Def.StatisticalMechanics.Code.FrontierD.FKRectAllSectorVerticalRate
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectAllSectorNormalization_vertical_negLog_tendsto_rate
    {q : Real} (hq : 4 < q) (r k : Nat) :
    Tendsto (fun m : Nat =>
      -Real.log (fkRectAllSectorNormalization
        (fkRectFixedChargeVerticalFamily r k m) q) /
          (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds (fkRectAllSectorNormalizationVerticalRate hq r k)) :=
  Classical.choose_spec
    (exists_fkRectAllSectorNormalization_vertical_negLogRate r k hq)

end
end StatMech.FrontierD
