/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part9


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexPositiveUnitComponentResidualMixedRouting

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


def nonHighToUnit
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (hrealizable : sixVertexPositiveUnitComponentResidualSource source.1) :
    SixVertexPositiveUnitComponentResidualSources T middle
      hmiddle_pos hmiddle_lt grade :=
  ⟨source.1, hrealizable, source.2⟩


def nonHighToGeometric
    (source : SixVertexHorizontalNotDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade)
    (hnotRealizable : ¬
      sixVertexPositiveUnitComponentResidualSource source.1) :
    SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade :=
  ⟨source.1, hnotRealizable, source.2⟩


end SixVertexPositiveUnitComponentResidualMixedRouting
end
end StatMech.FrontierD
