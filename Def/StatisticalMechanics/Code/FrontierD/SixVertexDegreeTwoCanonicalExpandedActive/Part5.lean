/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part4


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalExpandedActiveReturnState
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
  let input := sixVertexDegreeTwoCanonicalExpandedInputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer x
  let returned := sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega
    heta hdegree layer input
  if mask (doubledAlignedVertex returned) &&
      (fkMedialVertexParity (doubledAlignedVertex returned) == true) then
    doubledAlignedBranchSwap returned else returned

end
end StatMech.FrontierD
