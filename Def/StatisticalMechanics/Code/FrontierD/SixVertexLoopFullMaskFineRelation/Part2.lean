/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopFullUnitMaskTarget
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (certificate : SixVertexLoopFullUnitMask middle hmiddle_pos
      hmiddle_lt profile source) :
    SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile :=
  sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt
    profile source certificate.1 certificate.2.1 certificate.2.2

end
end StatMech.FrontierD
