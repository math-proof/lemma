/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexZeroDecorationEquivLoopPairings
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) :
    Fin (sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 0) ≃
      (SixVertexCompatibleLoopPairing pair.1.1 ×
        SixVertexCompatibleLoopPairing pair.2.1) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, Fintype.card_prod,
    card_sixVertexCompatibleLoopPairing pair.1.1 pair.1.2.1,
    card_sixVertexCompatibleLoopPairing pair.2.1 pair.2.2.1]
  simp [sixVertexMarkedPairMultiplicityNat, pow_add]


end
end StatMech.FrontierD
