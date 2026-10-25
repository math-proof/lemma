/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFullDisagreementColoredTarget_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) (layer : Bool) :
    (sixVertexFullDisagreementColoredTarget source mask hmask layer).arrows =
      if layer then
        sixVertexTorusSwitchSecond mask
          (source false).arrows (source true).arrows
      else sixVertexTorusSwitchFirst mask
          (source false).arrows (source true).arrows := by
  let vertexMask := sixVertexFullDisagreementVertexMask mask
  cases layer <;> apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_horizontal, Bool.false_eq_true, if_false]
    by_cases hdiff : (source false).arrows.horizontal v ≠
        (source true).arrows.horizontal v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdiff))
      change vertexMask v = mask.horizontal v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchFirst, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_vertical, Bool.false_eq_true, if_false]
    by_cases hdiff : (source false).arrows.vertical v ≠
        (source true).arrows.vertical v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdiff))
      change vertexMask v = mask.vertical v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchFirst, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_horizontal, if_true]
    by_cases hdiff : (source false).arrows.horizontal v ≠
        (source true).arrows.horizontal v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdiff))
      change vertexMask v = mask.horizontal v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchSecond, heq]
  · simp only [sixVertexFullDisagreementColoredTarget,
      fkColoredFullSwapTarget_vertical, if_true]
    by_cases hdiff : (source false).arrows.vertical v ≠
        (source true).arrows.vertical v
    · have hv := hmask.vertexMask_eq_localMask_of_disagrees (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            (source false).arrows (source true).arrows v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdiff))
      change vertexMask v = mask.vertical v at hv
      change (if vertexMask v then _ else _) = _
      rw [hv]
      rfl
    · have heq := not_ne_iff.mp hdiff
      simp [sixVertexTorusSwitchSecond, heq]

theorem sixVertexFullDisagreementColoredTarget_boundedFineRowProfile
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexFullDisagreementColoredTarget
            source mask hmask false).arrows.horizontal,
          (sixVertexFullDisagreementColoredTarget
            source mask hmask true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal) := by
  rw [sixVertexFullDisagreementColoredTarget_arrows,
    sixVertexFullDisagreementColoredTarget_arrows]
  exact hmask.boundedFineRowProfile

theorem sixVertexFullDisagreementColoredTarget_bigrade
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask) :
    (fkColoredLoopPairingPairTotalC
        (sixVertexFullDisagreementColoredTarget source mask hmask),
      fkColoredTrueStrandSlotCount
        (sixVertexFullDisagreementColoredTarget source mask hmask)) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  fkColoredFullSwapTarget_bigrade source _ _

theorem sixVertexFullDisagreementColoredTarget_middleSectors
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (source false).arrows (source true).arrows mask)
    (middle : Nat)
    (hlower : sixVertexUpCount
      (svTorusVerticalRows T (source false).arrows
        (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
      (svTorusVerticalRows T (source true).arrows
        (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (source false).arrows (source true).arrows = 1) :
    sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexFullDisagreementColoredTarget
            source mask hmask false).arrows
          (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
        (svTorusVerticalRows T
          (sixVertexFullDisagreementColoredTarget
            source mask hmask true).arrows
          (svFinLast T.height_pos)) = middle := by
  rw [sixVertexFullDisagreementColoredTarget_arrows,
    sixVertexFullDisagreementColoredTarget_arrows]
  constructor
  · have hcount := intCast_upCount_switchFirst_eq_add_seamTransfer
      mask (source false).arrows (source true).arrows
    rw [hlower, htransfer] at hcount
    have hnat : middle - 1 + 1 = middle :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hmiddle.ne')
    rw [← hnat]
    exact_mod_cast hcount
  · have hcount := intCast_upCount_switchSecond_eq_sub_seamTransfer
      mask (source false).arrows (source true).arrows
    rw [hupper, htransfer] at hcount
    have hcast : ((middle + 1 : Nat) : Int) - 1 = (middle : Int) := by
      omega
    rw [hcast] at hcount
    exact_mod_cast hcount


end
end StatMech.FrontierD
