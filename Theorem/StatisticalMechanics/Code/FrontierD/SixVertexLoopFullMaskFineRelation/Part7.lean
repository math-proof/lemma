/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part6


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexLoopFullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    (Finset.univ.filter
      (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).card =
      Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source) := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (sixVertexLoopFullUnitMaskEquivRelated
    middle hmiddle_pos hmiddle_lt profile source)).symm


theorem sixVertexLoopFullMaskFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    (Finset.univ.filter
      (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
    hmiddle_lt profile source mask hmask htransfer, ?_⟩
  simp [sixVertexLoopFullMaskFineRelated_target middle hmiddle_pos
    hmiddle_lt profile source mask hmask htransfer]


theorem sixVertexLoopFullMaskFineRelated_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    sixVertexLoopDecoratedPairBigrade target.1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  obtain ⟨mask, hmask, htransfer, rfl⟩ := hrelated
  exact sixVertexLoopDecoratedFullMaskTarget_bigrade middle hmiddle_pos
    hmiddle_lt source.1 mask hmask htransfer

theorem sixVertexLoopFullMaskFineRelated_twoCycle
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((sixVertexLoopDecoratedPairColored source.1 false).arrows,
        (sixVertexLoopDecoratedPairColored source.1 true).arrows)
      ((sixVertexLoopDecoratedPairColored target.1 false).arrows,
        (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  have hedge := certificate.2.1.pairAtMostTwoCycleFineRelated
  rw [← sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile source target hrelated,
    ← sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile source target hrelated] at hedge
  exact hedge


theorem rawFineProfile_of_fullMaskUnitDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨certificate⟩ := hne profile source
    exact sixVertexLoopFullMaskFineRelated_nonempty middle hmiddle_pos
      hmiddle_lt profile source certificate.1 certificate.2.1
        certificate.2.2
  · intro profile source target hrelated
    rw [card_sixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source]
    exact hdegree profile source target hrelated


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskUnitDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt
    hne hdegree


theorem rawFineProfile_of_fullMaskNegativePositiveDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hmaskDegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        Fintype.card (SixVertexLoopFullNegativeMask profile target) <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt hne
  intro profile source target hrelated
  exact (card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks
    middle hmiddle_pos hmiddle_lt profile target).trans
      (hmaskDegree profile source target hrelated)

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskNegativePositiveDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos
        hmiddle_lt profile source))
    (hmaskDegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        Fintype.card (SixVertexLoopFullNegativeMask profile target) <=
          Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos
            hmiddle_lt profile source)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_fullMaskNegativePositiveDegree middle
    hmiddle_pos hmiddle_lt hne hmaskDegree

end
end StatMech.FrontierD
