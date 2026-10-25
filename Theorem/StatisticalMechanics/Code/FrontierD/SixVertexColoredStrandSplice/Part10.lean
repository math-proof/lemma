/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredStrandSplice.target_totalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (hC : splice.PreservesTotalC) :
    fkColoredLoopPairingPairTotalC splice.target =
      fkColoredLoopPairingPairTotalC source := by
  rw [splice.target_totalC_eq_slotPairEqualCount, hC,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]

end
end StatMech.FrontierD
