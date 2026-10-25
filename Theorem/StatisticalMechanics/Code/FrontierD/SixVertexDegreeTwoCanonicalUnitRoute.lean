/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalUnitRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoOrderedStep_zeroOrUnit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 0 \/
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1 \/
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = -1 := by
  by_cases hzero :
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 0
  · exact Or.inl hzero
  · exact Or.inr
      (sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero
        hdegree dart hzero)

theorem sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 2 := by
  rw [sum_map_sixVertexDegreeTwoOrderedAllStrands]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree middle homegaSector hetaSector hmiddle


end
end StatMech.FrontierD
