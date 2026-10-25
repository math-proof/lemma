/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta
      hdegree middle homegaSector hetaSector hmiddle) : T.Vertex × Bool :=
  fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer) occurrence.1

end
end StatMech.FrontierD
