/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredVertexCrossTarget_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (fkColoredVertexCrossTarget source mask hbond) slot =
      fkColoredLayeredSlotColor source
        (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> cases hm : mask v <;>
    cases hfalse : (source false).pairing v <;>
    cases htrue : (source true).pairing v <;>
    simp [fkColoredLayeredSlotColor, fkColoredFullSwapLayeredSlotEquiv,
      fkColoredVertexCrossTarget, fkColoredVertexCrossRawColor,
      fkColoredLocalPairCrossIf, fkColoredLocalPairReconnection, hm,
      hfalse, htrue, FKColoredLoopPairing.localPairing,
      FKColoredLocalPairing.sideColor]

theorem fkColoredVertexCrossTarget_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    fkColoredTrueStrandSlotCount
        (fkColoredVertexCrossTarget source mask hbond) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (fkColoredFullSwapLayeredSlotEquiv mask)
  intro slot
  rw [fkColoredVertexCrossTarget_slotColor]

theorem fkColoredVertexCrossTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredVertexCrossBondCoherent source mask) :
    (fkColoredLoopPairingPairTotalC
        (fkColoredVertexCrossTarget source mask hbond),
      fkColoredTrueStrandSlotCount
        (fkColoredVertexCrossTarget source mask hbond)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  exact Prod.ext
    (fkColoredVertexCrossTarget_totalC source mask hbond)
    (fkColoredVertexCrossTarget_trueStrandSlotCount source mask hbond)


end
end StatMech.FrontierD
