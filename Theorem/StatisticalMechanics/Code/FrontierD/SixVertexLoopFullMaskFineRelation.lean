/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopDecoratedPairColored_injective
    {T : EvenTorus} {left right : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexLoopDecoratedPairColored :
        SixVertexLoopDecoratedPair T left right ->
          FKColoredLoopPairingPair T) := by
  intro first second h
  have hpair : first.1 = second.1 := by
    apply Prod.ext
    · apply Subtype.ext
      simpa using congrArg FKColoredLoopPairing.arrows (congrFun h false)
    · apply Subtype.ext
      simpa using congrArg FKColoredLoopPairing.arrows (congrFun h true)
  cases first with
  | mk firstPair firstDecoration =>
    cases second with
    | mk secondPair secondDecoration =>
      dsimp at hpair
      subst secondPair
      have hdecoration : firstDecoration = secondDecoration := by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg FKColoredLoopPairing.pairing (congrFun h false)
        · apply Subtype.ext
          exact congrArg FKColoredLoopPairing.pairing (congrFun h true)
      exact Sigma.ext rfl (heq_of_eq hdecoration)


theorem fkColoredFullSwapTarget_injective_fixedMask
    {T : EvenTorus} (mask : T.Vertex -> Bool)
    (first second : FKColoredLoopPairingPair T)
    (hfirst : FKColoredFullSwapBondCoherent first mask)
    (hsecond : FKColoredFullSwapBondCoherent second mask)
    (heq : fkColoredFullSwapTarget first mask hfirst =
      fkColoredFullSwapTarget second mask hsecond) :
    first = second := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : mask v = true
    · have hv := congrArg (fun target =>
          (target (!layer)).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm] using hv
    · have hv := congrArg (fun target => (target layer).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm] using hv
  · funext d
    by_cases hm : mask d.1 = true
    · have hd := congrArg (fun target => (target (!layer)).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm] using hd
    · have hd := congrArg (fun target => (target layer).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm] using hd

theorem fkColoredFullSwapTarget_injective_of_mask_eq
    {T : EvenTorus} (firstMask secondMask : T.Vertex -> Bool)
    (first second : FKColoredLoopPairingPair T)
    (hfirst : FKColoredFullSwapBondCoherent first firstMask)
    (hsecond : FKColoredFullSwapBondCoherent second secondMask)
    (hmasks : firstMask = secondMask)
    (heq : fkColoredFullSwapTarget first firstMask hfirst =
      fkColoredFullSwapTarget second secondMask hsecond) :
    first = second := by
  funext layer
  apply FKColoredLoopPairing.ext
  · funext v
    by_cases hm : firstMask v = true
    · have hmSecond : secondMask v = true := by rw [← hmasks]; exact hm
      have hv := congrArg (fun target =>
        (target (!layer)).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm, hmSecond] using hv
    · have hmSecond : secondMask v ≠ true := by
        rwa [← hmasks]
      have hv := congrArg (fun target => (target layer).pairing v) heq
      simpa [fkColoredFullSwapTarget_pairing, hm, hmSecond] using hv
  · funext d
    by_cases hm : firstMask d.1 = true
    · have hmSecond : secondMask d.1 = true := by rw [← hmasks]; exact hm
      have hd := congrArg (fun target => (target (!layer)).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm, hmSecond] using hd
    · have hmSecond : secondMask d.1 ≠ true := by
        rwa [← hmasks]
      have hd := congrArg (fun target => (target layer).color d) heq
      simpa [fkColoredFullSwapTarget_color, hm, hmSecond] using hd


theorem sixVertexTorusMaskSeamTransfer_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexTorusMaskSeamTransfer mask
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) =
      -sixVertexTorusMaskSeamTransfer mask omega eta := by
  unfold sixVertexTorusMaskSeamTransfer
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases hm : mask.vertical (i, svFinLast T.height_pos) <;>
    cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond, hm, ho, he]


theorem SixVertexFullDisagreementMask.pairSwitch
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    SixVertexFullDisagreementMask
      (sixVertexTorusSwitchFirst mask omega eta)
      (sixVertexTorusSwitchSecond mask omega eta) mask := by
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees,
      sixVertexTorusEdgeDisagrees_pairSwitch_iff]
    exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
      omega eta v d).1 (hmask.1 v d hd)
  · intro v d r hd hr
    apply hmask.2 v d r hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees] at hr ⊢
    exact (sixVertexTorusEdgeDisagrees_pairSwitch_iff
      mask omega eta _).1 hr


theorem SixVertexFullDisagreementMask.eq_fullDisagreementMask_switchFirst
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    mask = sixVertexFullDisagreementMask omega
      (sixVertexTorusSwitchFirst mask omega eta) := by
  apply SixVertexArrows.ext <;> funext v
  · by_cases hm : mask.horizontal v = true
    · have hdiff : omega.horizontal v ≠ eta.horizontal v := by
        simpa [sixVertexLocalIncomingPattern, fkLoopEastIncoming] using
          hmask.1 v 1 (by
            simpa [sixVertexTorusLocalSwitchMask] using hm)
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hm, hdiff]
    · have hmfalse : mask.horizontal v = false :=
        Bool.eq_false_of_not_eq_true hm
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hmfalse]
  · by_cases hm : mask.vertical v = true
    · have hdiff : omega.vertical v ≠ eta.vertical v := by
        simpa [sixVertexLocalIncomingPattern, fkLoopNorthIncoming] using
          hmask.1 v 3 (by
            simpa [sixVertexTorusLocalSwitchMask] using hm)
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hm, hdiff]
    · have hmfalse : mask.vertical v = false :=
        Bool.eq_false_of_not_eq_true hm
      simp [sixVertexFullDisagreementMask, sixVertexTorusSwitchFirst,
        hmfalse]


theorem sixVertexTorusSwitchFirst_injective_on_fullMasks
    {T : EvenTorus} {omega eta first second : SixVertexArrows T}
    (hfirst : SixVertexFullDisagreementMask omega eta first)
    (hsecond : SixVertexFullDisagreementMask omega eta second)
    (heq : sixVertexTorusSwitchFirst first omega eta =
      sixVertexTorusSwitchFirst second omega eta) :
    first = second := by
  calc
    first = sixVertexFullDisagreementMask omega
        (sixVertexTorusSwitchFirst first omega eta) :=
      hfirst.eq_fullDisagreementMask_switchFirst
    _ = sixVertexFullDisagreementMask omega
        (sixVertexTorusSwitchFirst second omega eta) := by rw [heq]
    _ = second := hsecond.eq_fullDisagreementMask_switchFirst.symm

theorem sixVertexPairUnionHorizontal_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexPairUnionHorizontal (omega, eta) =
      sixVertexPairUnionHorizontal
        (sixVertexTorusSwitchFirst mask omega eta,
          sixVertexTorusSwitchSecond mask omega eta) := by
  funext v
  unfold sixVertexPairUnionHorizontal
  by_cases hm : mask.horizontal v = true <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      hm, add_comm]

theorem sixVertexPairUnionVertical_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexPairUnionVertical (omega, eta) =
      sixVertexPairUnionVertical
        (sixVertexTorusSwitchFirst mask omega eta,
          sixVertexTorusSwitchSecond mask omega eta) := by
  funext v
  unfold sixVertexPairUnionVertical
  by_cases hm : mask.vertical v = true <;>
    simp [sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
      hm, add_comm]


theorem SixVertexFullDisagreementMask.pairAtMostTwoCycleFineRelated
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    sixVertexPairAtMostTwoCycleFineRelated (omega, eta)
      (sixVertexTorusSwitchFirst mask omega eta,
        sixVertexTorusSwitchSecond mask omega eta) := by
  constructor
  · apply sixVertexPairAtMostTwoCycleRelated_of_union_eq
    · exact sixVertexPairUnionHorizontal_pairSwitch mask omega eta
    · exact sixVertexPairUnionVertical_pairSwitch mask omega eta
  · exact hmask.boundedFineRowProfile.symm


theorem sixVertexLexDisagreementComponentMask_full
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    SixVertexFullDisagreementMask omega eta
      (sixVertexLexDisagreementComponentMask T omega eta h) := by
  constructor
  · intro v d hd
    rw [sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    apply sixVertexLexDisagreementComponentMask_selects_only_disagreement
      T omega eta h
    rw [← sixVertexTorusLocalSwitchMask_apply]
    exact hd
  · intro v d r hd hr
    exact sixVertexLexDisagreementComponentMask_incident_closure
      T omega eta h v d r hd hr


end
end StatMech.FrontierD
