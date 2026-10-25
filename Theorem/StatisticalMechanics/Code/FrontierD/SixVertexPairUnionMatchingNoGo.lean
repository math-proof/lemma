/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPairSwitch_eq_target_of_union_eq
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T)
    (hhorizontal : sixVertexPairUnionHorizontal source =
      sixVertexPairUnionHorizontal target)
    (hvertical : sixVertexPairUnionVertical source =
      sixVertexPairUnionVertical target) :
    sixVertexTorusSwitchFirst
          (sixVertexPairSwitchMaskToTarget source target)
          source.1 source.2 = target.1 /\
      sixVertexTorusSwitchSecond
          (sixVertexPairSwitchMaskToTarget source target)
          source.1 source.2 = target.2 := by
  constructor <;> apply SixVertexArrows.ext
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontal at h
    generalize hs₁ : source.1.horizontal v = s₁ at h ⊢
    generalize hs₂ : source.2.horizontal v = s₂ at h ⊢
    generalize ht₁ : target.1.horizontal v = t₁ at h ⊢
    generalize ht₂ : target.2.horizontal v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchFirst,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVertical at h
    generalize hs₁ : source.1.vertical v = s₁ at h ⊢
    generalize hs₂ : source.2.vertical v = s₂ at h ⊢
    generalize ht₁ : target.1.vertical v = t₁ at h ⊢
    generalize ht₂ : target.2.vertical v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchFirst,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hhorizontal v
    unfold sixVertexPairUnionHorizontal at h
    generalize hs₁ : source.1.horizontal v = s₁ at h ⊢
    generalize hs₂ : source.2.horizontal v = s₂ at h ⊢
    generalize ht₁ : target.1.horizontal v = t₁ at h ⊢
    generalize ht₂ : target.2.horizontal v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchSecond,
        sixVertexPairSwitchMaskToTarget]
  · funext v
    have h := congrFun hvertical v
    unfold sixVertexPairUnionVertical at h
    generalize hs₁ : source.1.vertical v = s₁ at h ⊢
    generalize hs₂ : source.2.vertical v = s₂ at h ⊢
    generalize ht₁ : target.1.vertical v = t₁ at h ⊢
    generalize ht₂ : target.2.vertical v = t₂ at h ⊢
    cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;>
      simp_all [sixVertexTorusSwitchSecond,
        sixVertexPairSwitchMaskToTarget]


theorem sixVertexFourByTwo_no_unionEqual_middlePair
    (alpha beta : SixVertexArrows sixVertexFourByTwoTorus)
    (halphaIce : alpha.IceRule) (hbetaIce : beta.IceRule)
    (halphaSector : sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus alpha
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1)
    (hhorizontal : sixVertexPairUnionHorizontal
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) =
      sixVertexPairUnionHorizontal (alpha, beta))
    (hvertical : sixVertexPairUnionVertical
        (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) =
      sixVertexPairUnionVertical (alpha, beta)) : False := by
  let source :=
    (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
  let target := (alpha, beta)
  let mask := sixVertexPairSwitchMaskToTarget source target
  obtain ⟨hfirst, hsecond⟩ :=
    sixVertexPairSwitch_eq_target_of_union_eq
      source target hhorizontal hvertical
  apply sixVertexFourByTwo_no_icePairSwitch_to_middle mask
  rw [hfirst, hsecond]
  exact ⟨halphaIce, hbetaIce, halphaSector⟩

end
end StatMech.FrontierD
