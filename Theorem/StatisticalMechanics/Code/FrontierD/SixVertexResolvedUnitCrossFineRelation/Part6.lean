/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopResolvedUnitCrossOfRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    target = sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle
      hmiddle_pos hmiddle_lt profile source
        (sixVertexLoopResolvedUnitCrossOfRelated middle hmiddle_pos
          hmiddle_lt profile source target hrelated) :=
  hrelated.choose_spec

theorem sixVertexLoopResolvedUnitCrossFineRelated_bigrade
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    sixVertexLoopDecoratedPairBigrade target.1 =
      sixVertexLoopDecoratedPairBigrade source.1 := by
  rw [sixVertexLoopResolvedUnitCrossOfRelated_target middle hmiddle_pos
    hmiddle_lt profile source target hrelated]
  exact sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade middle
    hmiddle_pos hmiddle_lt profile source _

theorem sixVertexLoopResolvedUnitCrossFineRelated_twoCycle
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle
      hmiddle_pos hmiddle_lt profile source target) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((sixVertexLoopDecoratedPairColored source.1 false).arrows,
        (sixVertexLoopDecoratedPairColored source.1 true).arrows)
      ((sixVertexLoopDecoratedPairColored target.1 false).arrows,
        (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
  let cross := sixVertexLoopResolvedUnitCrossOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  have htarget := congrArg (fun decorated =>
      sixVertexLoopDecoratedPairColored decorated.1)
    (sixVertexLoopResolvedUnitCrossOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source target hrelated)
  change sixVertexLoopDecoratedPairColored target.1 =
    sixVertexLoopDecoratedPairColored
      (sixVertexLoopDecoratedResolvedUnitCrossTarget middle hmiddle_pos
        hmiddle_lt source.1 cross) at htarget
  rw [sixVertexLoopDecoratedResolvedUnitCrossTarget_colored] at htarget
  rw [htarget]
  exact cross.target_twoCycleFine


theorem rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
          hmiddle_lt profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨cross⟩ := hne profile source
    exact sixVertexLoopResolvedUnitCrossFineRelated_nonempty middle
      hmiddle_pos hmiddle_lt profile source cross
  · exact hdegree

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedUnitCrossRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredResolvedUnitCross
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall
      (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
      (target : SixVertexLoopDecoratedPairFineProfileFiber
        T middle middle profile),
      SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
          hmiddle_lt profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos
            hmiddle_lt profile source)).card) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_rawFineProfile
    T middle hmiddle_pos hmiddle_lt
  exact rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree middle
    hmiddle_pos hmiddle_lt hne hdegree

end
end StatMech.FrontierD
