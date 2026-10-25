/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem FKColoredLoopPairing.toCompatible_toColored
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    colored.toCompatible.toColored = colored := by
  apply FKColoredLoopPairing.ext
  · rfl
  · funext d
    change (fkMedialCheckerColor d ^^
        fkMedialDartIncoming colored.arrows d) = colored.color d
    rw [colored.dartIncoming_arrows]
    change (fkMedialCheckerColor d ^^
        (fkMedialCheckerColor d ^^ colored.color d)) = colored.color d
    generalize hc : fkMedialCheckerColor d = c
    generalize hm : colored.color d = m
    cases c <;> cases m <;> rfl


end
end StatMech.FrontierD
