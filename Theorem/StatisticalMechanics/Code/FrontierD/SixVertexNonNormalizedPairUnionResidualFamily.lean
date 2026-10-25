/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexNonNormalizedUnitChargeResidualSources.unitCharge
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    sixVertexHorizontalDegreeTwoUnitCharge source.1.1 :=
  sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge source.1.1
    source.2 source.1.2.2


end
end StatMech.FrontierD
