/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting


namespace StatMech.FrontierD

noncomputable section

inductive SixVertexPositiveUnitComponentResidualGeometricSourceKind
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) : Type
  | nonDegreeTwo
      (notDegreeTwo : ¬ SixVertexLocallyDegreeTwo
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
  | nonNormalizedUnitCharge
      (degreeTwo : SixVertexLocallyDegreeTwo
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
        (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1)
      (unitCharge : sixVertexHorizontalDegreeTwoUnitCharge source.1)


end
end StatMech.FrontierD
