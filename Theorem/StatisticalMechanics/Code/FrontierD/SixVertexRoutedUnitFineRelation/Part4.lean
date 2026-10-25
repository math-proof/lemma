/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopRoutedUnitFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey
      (sixVertexLoopDecoratedPairColored source.1)) :
    (Finset.univ.filter (SixVertexLoopRoutedUnitFineRelated middle
      hmiddle_pos hmiddle_lt profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedRoutedUnitFineTarget middle hmiddle_pos
    hmiddle_lt profile source key, ?_⟩
  simp [SixVertexLoopRoutedUnitFineRelated]

theorem rawFineProfile_of_routedUnitRelationEdgeDegree
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T)
      (source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile),
      Nonempty (FKColoredFineTwoCycleUnitTransferRoutedKey
        (sixVertexLoopDecoratedPairColored source.1)))
    (hdegree : forall profile source target,
      SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
          profile source target ->
        (Finset.univ.filter fun otherSource =>
          SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
            profile otherSource target).card <=
        (Finset.univ.filter
          (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt
            profile source)).card) :
    forall profile : SixVertexHorizontalBoundedFineRowProfile T,
      0 <= sixVertexHorizontalFineRowProfileSignedSum T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        middle middle profile := by
  apply rawFineProfile_of_loopRelationEdgeDegree
    (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt)
  · intro profile source
    obtain ⟨key⟩ := hne profile source
    exact sixVertexLoopRoutedUnitFineRelated_nonempty middle hmiddle_pos
      hmiddle_lt profile source key
  · exact hdegree

end
end StatMech.FrontierD
