/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopFullUnitMaskTarget_injective
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    Function.Injective (sixVertexLoopFullUnitMaskTarget middle
      hmiddle_pos hmiddle_lt profile source) := by
  intro first second heq
  apply Subtype.ext
  apply sixVertexTorusSwitchFirst_injective_on_fullMasks
      first.2.1 second.2.1
  have harrows := congrArg (fun target =>
    (sixVertexLoopDecoratedPairColored target.1 false).arrows) heq
  simpa only [sixVertexLoopFullUnitMaskTarget,
    sixVertexLoopDecoratedFullMaskFineTarget_false_arrows] using harrows


end
end StatMech.FrontierD
