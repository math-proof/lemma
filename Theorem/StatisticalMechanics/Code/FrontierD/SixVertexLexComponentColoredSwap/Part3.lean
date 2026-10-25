/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLexDisagreementComponentColoredTarget_false_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    (sixVertexLexDisagreementComponentColoredTarget source h false).arrows =
      sixVertexTorusSwitchFirst
        (sixVertexLexDisagreementComponentMask T
          (source false).arrows (source true).arrows h)
        (source false).arrows (source true).arrows := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_horizontal]
    change (if vertexMask v then eta.horizontal v else omega.horizontal v) = _
    unfold sixVertexTorusSwitchFirst
    by_cases hdisagrees : omega.horizontal v ≠ eta.horizontal v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdisagrees))
      change vertexMask v = edgeMask.horizontal v at hmask
      rw [hmask]
    · have heq : omega.horizontal v = eta.horizontal v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_vertical]
    change (if vertexMask v then eta.vertical v else omega.vertical v) = _
    unfold sixVertexTorusSwitchFirst
    by_cases hdisagrees : omega.vertical v ≠ eta.vertical v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdisagrees))
      change vertexMask v = edgeMask.vertical v at hmask
      rw [hmask]
    · have heq : omega.vertical v = eta.vertical v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]

theorem sixVertexLexDisagreementComponentColoredTarget_true_arrows
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty) :
    (sixVertexLexDisagreementComponentColoredTarget source h true).arrows =
      sixVertexTorusSwitchSecond
        (sixVertexLexDisagreementComponentMask T
          (source false).arrows (source true).arrows h)
        (source false).arrows (source true).arrows := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let edgeMask := sixVertexLexDisagreementComponentMask T omega eta h
  let vertexMask := sixVertexLexDisagreementComponentVertexMask
    T omega eta h
  apply SixVertexArrows.ext <;> funext v
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_horizontal]
    change (if vertexMask v then omega.horizontal v else eta.horizontal v) = _
    unfold sixVertexTorusSwitchSecond
    by_cases hdisagrees : omega.horizontal v ≠ eta.horizontal v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 1)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 1).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopEastIncoming] using hdisagrees))
      change vertexMask v = edgeMask.horizontal v at hmask
      rw [hmask]
    · have heq : omega.horizontal v = eta.horizontal v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]
  · simp only [sixVertexLexDisagreementComponentColoredTarget,
      fkColoredFullSwapTarget_vertical]
    change (if vertexMask v then omega.vertical v else eta.vertical v) = _
    unfold sixVertexTorusSwitchSecond
    by_cases hdisagrees : omega.vertical v ≠ eta.vertical v
    · have hmask :=
        sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees
          T omega eta h (v, 3)
          ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
            omega eta v 3).1 (by
              simpa [sixVertexLocalIncomingPattern,
                fkLoopNorthIncoming] using hdisagrees))
      change vertexMask v = edgeMask.vertical v at hmask
      rw [hmask]
    · have heq : omega.vertical v = eta.vertical v :=
        not_ne_iff.mp hdisagrees
      simp [omega, eta, heq]


theorem sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (middle : Nat)
    (hlower : sixVertexUpCount
      (svTorusVerticalRows T (source false).arrows
        (svFinLast T.height_pos)) = middle - 1)
    (hupper : sixVertexUpCount
      (svTorusVerticalRows T (source true).arrows
        (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (h : (sixVertexPositiveSeamDisagreements T
      (source false).arrows (source true).arrows).Nonempty)
    (htransfer : sixVertexTorusMaskSeamTransfer
      (sixVertexLexDisagreementComponentMask T
        (source false).arrows (source true).arrows h)
      (source false).arrows (source true).arrows = 1) :
    let target := sixVertexLexDisagreementComponentColoredTarget source h
    sixVertexUpCount
          (svTorusVerticalRows T (target false).arrows
            (svFinLast T.height_pos)) = middle /\
      sixVertexUpCount
          (svTorusVerticalRows T (target true).arrows
            (svFinLast T.height_pos)) = middle /\
      sixVertexHorizontalPairBoundedFineRowProfile
          ((target false).arrows.horizontal,
            (target true).arrows.horizontal) =
        sixVertexHorizontalPairBoundedFineRowProfile
          ((source false).arrows.horizontal,
            (source true).arrows.horizontal) := by
  let omega := (source false).arrows
  let eta := (source true).arrows
  let target := sixVertexLexDisagreementComponentColoredTarget source h
  have hmiddleSectors :=
    sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one
      T omega eta middle (source false).iceRule (source true).iceRule
      hlower hupper hmiddle h htransfer
  dsimp only at hmiddleSectors ⊢
  rw [sixVertexLexDisagreementComponentColoredTarget_false_arrows,
    sixVertexLexDisagreementComponentColoredTarget_true_arrows]
  refine ⟨hmiddleSectors.2.2.1, hmiddleSectors.2.2.2, ?_⟩
  exact sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile
    T omega eta h

end
end StatMech.FrontierD
