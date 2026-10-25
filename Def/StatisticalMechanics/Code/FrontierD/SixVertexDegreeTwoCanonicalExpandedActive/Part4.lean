/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part3


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalExpandedSourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  if layer then sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta
    hdegree x else doubledAlignedFirstReturnPerm homega heta hdegree x

noncomputable def sixVertexDegreeTwoCanonicalExpandedOutputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  if mask (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x

end
end StatMech.FrontierD
