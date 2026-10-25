/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoBranchClosedSelected_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedBranchSwap x) =
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle x := by
  unfold sixVertexDegreeTwoBranchClosedSelected
  apply Bool.decide_congr
  exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle x


end
end StatMech.FrontierD
