/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoBranchClosedTransitionBit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) : Bool :=
  sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle x !=
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm x)


def sixVertexDegreeTwoBranchClosedSynchronizedAt
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta) :
    Prop :=
  sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
      homegaSector hetaSector hmiddle (d, false) =
    sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
      homegaSector hetaSector hmiddle (d, true)


end
end StatMech.FrontierD
