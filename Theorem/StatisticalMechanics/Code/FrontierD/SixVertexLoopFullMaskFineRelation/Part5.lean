/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopFullUnitMaskOfRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    target = sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
      profile source (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
        hmiddle_lt profile source target hrelated) := by
  exact hrelated.choose_spec.choose_spec.choose_spec

theorem sixVertexLoopFullUnitMaskOfRelated_false_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    (sixVertexLoopDecoratedPairColored target.1 false).arrows =
      sixVertexTorusSwitchFirst certificate.1
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    (sixVertexLoopDecoratedPairColored target.1 false).arrows =
        (sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 false).arrows :=
      congrArg (fun decorated =>
        (sixVertexLoopDecoratedPairColored decorated.1 false).arrows)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskFineTarget_false_arrows
      middle hmiddle_pos hmiddle_lt profile source _ _ _

theorem sixVertexLoopFullUnitMaskOfRelated_true_arrows
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    (sixVertexLoopDecoratedPairColored target.1 true).arrows =
      sixVertexTorusSwitchSecond certificate.1
        (sixVertexLoopDecoratedPairColored source.1 false).arrows
        (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    (sixVertexLoopDecoratedPairColored target.1 true).arrows =
        (sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 true).arrows :=
      congrArg (fun decorated =>
        (sixVertexLoopDecoratedPairColored decorated.1 true).arrows)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskFineTarget_true_arrows
      middle hmiddle_pos hmiddle_lt profile source _ _ _

theorem sixVertexLoopFullUnitMaskOfRelated_colored
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
      hmiddle_lt profile source target hrelated
    sixVertexLoopDecoratedPairColored target.1 =
      sixVertexFullDisagreementColoredTarget
        (sixVertexLoopDecoratedPairColored source.1)
        certificate.1 certificate.2.1 := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target hrelated
  calc
    sixVertexLoopDecoratedPairColored target.1 =
        sixVertexLoopDecoratedPairColored
          (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt
            profile source certificate).1 :=
      congrArg (fun decorated =>
        sixVertexLoopDecoratedPairColored decorated.1)
        (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
          hmiddle_lt profile source target hrelated)
    _ = _ := sixVertexLoopDecoratedFullMaskTarget_colored middle
      hmiddle_pos hmiddle_lt source.1 certificate.1
        certificate.2.1 certificate.2.2


end
end StatMech.FrontierD
