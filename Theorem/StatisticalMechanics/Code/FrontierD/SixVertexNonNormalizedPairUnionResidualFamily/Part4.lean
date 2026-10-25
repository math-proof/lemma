/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily.Part3


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexNonNormalizedPairUnionPhysicalTargetFamily

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


@[simp] theorem geometricRepair_target
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    (family.geometricRepair source branch).target =
      family.surplusTarget (source, branch) :=
  rfl

end SixVertexNonNormalizedPairUnionPhysicalTargetFamily
end
end StatMech.FrontierD
