/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedUnitTransferFineTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile := by
  let colored := sixVertexLoopDecoratedPairColored source.1
  let h := sixVertexLoopDecoratedPositiveSeam
    middle hmiddle_pos hmiddle_lt source.1
  let target := sixVertexLoopDecoratedUnitTransferTarget middle
    hmiddle_pos hmiddle_lt source.1 hunit
  have htarget :=
    sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one
      colored middle.val
      (by simpa [colored, sixVertexHorizontalLowerSector] using
        source.1.1.1.2.2)
      (by simpa [colored, sixVertexHorizontalUpperSector] using
        source.1.1.2.2.2)
      hmiddle_pos h hunit
  refine ⟨target, ?_⟩
  have hfine := htarget.2.2
  rw [← sixVertexLoopDecoratedUnitTransferTarget_colored
    middle hmiddle_pos hmiddle_lt source.1 hunit] at hfine
  exact hfine.trans source.2


def SixVertexLoopLexUnitFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber
      T middle middle profile) : Prop :=
  exists hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1,
    target = sixVertexLoopDecoratedUnitTransferFineTarget middle
      hmiddle_pos hmiddle_lt profile source hunit

end
end StatMech.FrontierD
