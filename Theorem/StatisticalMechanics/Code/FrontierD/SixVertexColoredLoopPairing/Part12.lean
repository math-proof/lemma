/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part9


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredLocalPairCrossIf_involutive
    (cross : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCrossIf cross
        (fkColoredLocalPairCrossIf cross pair) = pair := by
  cases cross <;> simp [fkColoredLocalPairCrossIf]

theorem fkColoredLocalPairCrossIf_pairing
    (cross layer : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    (if layer then (fkColoredLocalPairCrossIf cross pair).2.pairing
      else (fkColoredLocalPairCrossIf cross pair).1.pairing) =
    (if layer then pair.2.pairing else pair.1.pairing) := by
  cases cross <;> cases layer <;>
    simp [fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection]

end
end StatMech.FrontierD
