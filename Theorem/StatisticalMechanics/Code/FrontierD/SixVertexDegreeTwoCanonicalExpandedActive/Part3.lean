/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedInputState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
      homegaSector hetaSector hmiddle layer x).1 = x.1 := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedInputState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) = x := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

end
end StatMech.FrontierD
