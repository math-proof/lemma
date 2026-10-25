/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part11


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


noncomputable def toHighChargeHallRouting
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHighChargeHallRouting T middle
      hmiddle_pos hmiddle_lt grade where
  direct := routing.direct
  direct_injective := routing.direct_injective
  direct_supported := routing.direct_supported
  paired := routing.paired
  paired_distinct := routing.paired_distinct
  paired_supported := routing.paired_supported
  paired_output_recovers_occurrence :=
    routing.paired_output_recovers_occurrence
  paired_injective_with_occurrence := routing.paired_injective_with_occurrence
  direct_paired_disjoint := routing.direct_paired_disjoint


noncomputable def toTokenComponents
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalTwoCycleTokenReconnectionComponents T middle
      hmiddle_pos hmiddle_lt grade :=
  routing.toHighChargeHallRouting.toTokenComponents

end SixVertexPositiveUnitComponentResidualMixedRouting


def SixVertexPositiveUnitComponentResidualMixedRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  ∀ grade, Nonempty
    (SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
