/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalUnitPrefix_sum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 :=
  sixVertexCanonicalUnitItemPrefix_sum _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitSuffix_sum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 :=
  sixVertexCanonicalUnitItemSuffix_sum _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitPrefix_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle ≠ [] :=
  sixVertexCanonicalUnitItemPrefix_ne_nil _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitSuffix_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
      homegaSector hetaSector hmiddle ≠ [] :=
  sixVertexCanonicalUnitItemSuffix_ne_nil _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitPrefix_append_suffix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle ++
      sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
        homegaSector hetaSector hmiddle =
      sixVertexDegreeTwoOrderedAllStrands homega heta hdegree :=
  List.take_append_drop _ _

end
end StatMech.FrontierD
