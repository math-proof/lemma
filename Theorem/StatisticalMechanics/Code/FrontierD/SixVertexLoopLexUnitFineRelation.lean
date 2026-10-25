/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopLexUnitFineRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile
      source (sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit) := by
  exact ⟨hunit, rfl⟩

theorem sixVertexLoopLexUnitFineRelated_iff_eq
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile
        source target ↔
      target = sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit := by
  constructor
  · rintro ⟨other, rfl⟩
    congr
  · intro htarget
    exact ⟨hunit, htarget⟩


theorem sixVertexLoopLexUnitFineRelated_nonempty
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    (Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).Nonempty := by
  refine ⟨sixVertexLoopDecoratedUnitTransferFineTarget middle
    hmiddle_pos hmiddle_lt profile source hunit, ?_⟩
  simp [sixVertexLoopLexUnitFineRelated_target middle hmiddle_pos
    hmiddle_lt profile source hunit]


theorem card_sixVertexLoopLexUnitFineRelated_eq_one
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    (Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source)).card = 1 := by
  classical
  rw [show Finset.univ.filter
      (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt
        profile source) =
      {sixVertexLoopDecoratedUnitTransferFineTarget middle
        hmiddle_pos hmiddle_lt profile source hunit} by
    ext target
    simp [sixVertexLoopLexUnitFineRelated_iff_eq middle hmiddle_pos
      hmiddle_lt profile source target hunit]]
  simp

end
end StatMech.FrontierD
