/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexLoopFullNegativeMaskOfPreimage_val
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (preimage : {source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile //
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target}) :
    (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos
      hmiddle_lt profile target preimage).1 =
        (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt
          profile preimage.1 target preimage.2).1 := rfl


theorem sixVertexLoopFullNegativeMaskOfPreimage_injective
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile) :
    Function.Injective (sixVertexLoopFullNegativeMaskOfPreimage middle
      hmiddle_pos hmiddle_lt profile target) := by
  intro first second heq
  let firstCertificate := sixVertexLoopFullUnitMaskOfRelated middle
    hmiddle_pos hmiddle_lt profile first.1 target first.2
  let secondCertificate := sixVertexLoopFullUnitMaskOfRelated middle
    hmiddle_pos hmiddle_lt profile second.1 target second.2
  have hmask : firstCertificate.1 = secondCertificate.1 := by
    have := congrArg Subtype.val heq
    simpa [firstCertificate, secondCertificate] using this
  have hfirst := sixVertexLoopFullUnitMaskOfRelated_colored middle
    hmiddle_pos hmiddle_lt profile first.1 target first.2
  have hsecond := sixVertexLoopFullUnitMaskOfRelated_colored middle
    hmiddle_pos hmiddle_lt profile second.1 target second.2
  dsimp only at hfirst hsecond
  apply Subtype.ext
  apply Subtype.ext
  apply sixVertexLoopDecoratedPairColored_injective
  apply fkColoredFullSwapTarget_injective_of_mask_eq
    (sixVertexFullDisagreementVertexMask firstCertificate.1)
    (sixVertexFullDisagreementVertexMask secondCertificate.1)
    (sixVertexLoopDecoratedPairColored first.1.1)
    (sixVertexLoopDecoratedPairColored second.1.1)
    (firstCertificate.2.1.fullSwapBondCoherent
      (sixVertexLoopDecoratedPairColored first.1.1) firstCertificate.1)
    (secondCertificate.2.1.fullSwapBondCoherent
      (sixVertexLoopDecoratedPairColored second.1.1) secondCertificate.1)
    (congrArg sixVertexFullDisagreementVertexMask hmask)
  exact hfirst.symm.trans hsecond

theorem card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile) :
    (Finset.univ.filter fun source :
        SixVertexLoopDecoratedPairFineProfileFiber T
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) profile =>
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target).card <=
      Fintype.card (SixVertexLoopFullNegativeMask profile target) := by
  have hcard := Fintype.card_le_of_injective
    (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos
      hmiddle_lt profile target)
    (sixVertexLoopFullNegativeMaskOfPreimage_injective middle hmiddle_pos
      hmiddle_lt profile target)
  simpa only [Fintype.card_subtype] using hcard


end
end StatMech.FrontierD
