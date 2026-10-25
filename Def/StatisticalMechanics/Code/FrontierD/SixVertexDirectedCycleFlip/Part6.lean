/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusFlipSeamDelta
    {T : EvenTorus} (mask omega : SixVertexArrows T) : Int :=
  Finset.univ.sum (fun column : Fin T.width =>
    Int.ofNat ((sixVertexTorusFlip mask omega).vertical
      (column, svFinLast T.height_pos)).toNat -
    Int.ofNat (omega.vertical
      (column, svFinLast T.height_pos)).toNat)


end
end StatMech.FrontierD
