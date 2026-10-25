/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoCanonicalUnitCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) : Nat :=
  sixVertexCanonicalUnitItemPrefixLength
    (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree)
    (sixVertexDegreeTwoStrandStepSeamSign hdegree)
    (fun dart _ => sixVertexDegreeTwoOrderedStep_zeroOrUnit hdegree dart)
    (sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two
      homega heta hdegree middle homegaSector hetaSector hmiddle)


noncomputable def sixVertexDegreeTwoCanonicalUnitPrefix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).take
    (sixVertexDegreeTwoCanonicalUnitCut homega heta hdegree middle
      homegaSector hetaSector hmiddle)


noncomputable def sixVertexDegreeTwoCanonicalUnitSuffix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).drop
    (sixVertexDegreeTwoCanonicalUnitCut homega heta hdegree middle
      homegaSector hetaSector hmiddle)

end
end StatMech.FrontierD
