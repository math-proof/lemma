/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredFullSwapTarget_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (fkColoredFullSwapTarget source mask hbond) slot =
      fkColoredLayeredSlotColor source
        (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
  rcases slot with ⟨layer, v, side⟩
  by_cases hm : mask v <;> cases layer <;> cases side <;>
    simp [fkColoredLayeredSlotColor, fkColoredFullSwapLayeredSlotEquiv,
      fkColoredFullSwapTarget, hm]

theorem fkColoredFullSwapTarget_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredTrueStrandSlotCount
        (fkColoredFullSwapTarget source mask hbond) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (fkColoredFullSwapLayeredSlotEquiv mask)
  intro slot
  rw [fkColoredFullSwapTarget_slotColor]

theorem fkColoredFullSwapTarget_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    fkColoredLoopPairingPairTotalC
        (fkColoredFullSwapTarget source mask hbond) =
      fkColoredLoopPairingPairTotalC source := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
  rw [<- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(fkColoredFullSwapTarget source mask hbond false).cType_iff_color_west_eq_east,
    (fkColoredFullSwapTarget source mask hbond true).cType_iff_color_west_eq_east,
    (source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hm : mask v <;>
    by_cases hw : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases ht : (source true).color (v, .west) =
      (source true).color (v, .east) <;>
    simp [fkColoredFullSwapTarget, hm, add_comm, hw, ht]

theorem fkColoredFullSwapTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : T.Vertex -> Bool)
    (hbond : FKColoredFullSwapBondCoherent source mask) :
    (fkColoredLoopPairingPairTotalC
        (fkColoredFullSwapTarget source mask hbond),
      fkColoredTrueStrandSlotCount
        (fkColoredFullSwapTarget source mask hbond)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  rw [fkColoredFullSwapTarget_totalC,
    fkColoredFullSwapTarget_trueStrandSlotCount]

end
end StatMech.FrontierD
