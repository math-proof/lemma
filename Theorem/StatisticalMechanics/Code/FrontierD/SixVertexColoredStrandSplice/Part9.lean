/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairTotalC source =
      fkColoredSlotPairEqualCount source (Equiv.refl _) := by
  unfold fkColoredLoopPairingPairTotalC sixVertexTorusCTypeCount
    fkColoredSlotPairEqualCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [(source false).cType_iff_color_west_eq_east,
    (source true).cType_iff_color_west_eq_east]
  by_cases hfalse : (source false).color (v, .west) =
      (source false).color (v, .east) <;>
    by_cases htrue : (source true).color (v, .west) =
      (source true).color (v, .east) <;>
    simp [fkColoredLayeredSlotColor, hfalse, htrue]

theorem FKColoredStrandSplice.target_totalC_eq_slotPairEqualCount
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) :
    fkColoredLoopPairingPairTotalC splice.target =
      fkColoredSlotPairEqualCount source splice.slotEquiv := by
  rw [fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]
  unfold fkColoredSlotPairEqualCount
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Equiv.refl_apply]
  simp only [splice.target_slotColor]

end
end StatMech.FrontierD
