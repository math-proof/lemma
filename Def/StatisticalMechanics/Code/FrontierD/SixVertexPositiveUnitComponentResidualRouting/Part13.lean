/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part10


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


noncomputable def direct
    (routing : SixVertexPositiveUnitComponentResidualMixedRouting T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
      hmiddle_pos hmiddle_lt grade :=
  if hrealizable :
      sixVertexPositiveUnitComponentResidualSource source.1 then
    routing.unit.matching (nonHighToUnit source hrealizable)
  else (routing.geometric
    (nonHighToGeometric source hrealizable)).target

end SixVertexPositiveUnitComponentResidualMixedRouting
end
end StatMech.FrontierD
