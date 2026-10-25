/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part7


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkColoredLocalPairCross_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCross (fkColoredLocalPairCross pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

@[simp] theorem fkColoredLocalPairCrossWest_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairCrossWest (fkColoredLocalPairCrossWest pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

@[simp] theorem fkColoredLocalPairOddCross_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairOddCross (fkColoredLocalPairOddCross pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  cases a <;> cases c <;> rfl

@[simp] theorem fkColoredLocalPairReconnection_involutive
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    fkColoredLocalPairReconnection
        (fkColoredLocalPairReconnection pair) = pair := by
  rcases pair with ⟨⟨p, a, b⟩, ⟨q, c, d⟩⟩
  rfl

end
end StatMech.FrontierD
