/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily.Part2


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexNonNormalizedPairUnionPhysicalTargetFamily

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


noncomputable def surplusEmbedding
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade) :
    (SixVertexNonNormalizedUnitChargeResidualSources T middle
        hmiddle_pos hmiddle_lt grade × Bool) ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade where
  toFun := family.surplusTarget
  inj' := by
    intro first second heq
    apply family.target.injective
    rw [← family.surplusTarget_physical first,
      ← family.surplusTarget_physical second]
    exact congrArg sixVertexHorizontalActualSurplusConfigurationPair heq


noncomputable def decoder
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (target : SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade) :
    Option (SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) :=
  if h : ∃ coded, family.surplusEmbedding coded = target then
    some (Classical.choose h).1.1.1
  else none


end SixVertexNonNormalizedPairUnionPhysicalTargetFamily
end
end StatMech.FrontierD
