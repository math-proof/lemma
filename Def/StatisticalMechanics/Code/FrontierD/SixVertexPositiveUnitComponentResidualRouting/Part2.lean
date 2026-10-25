/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Inductive.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting


namespace StatMech.FrontierD

noncomputable section

noncomputable def
    sixVertexPositiveUnitComponentResidualGeometricSourceKind
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade) :
    SixVertexPositiveUnitComponentResidualGeometricSourceKind source := by
  let pair := sixVertexHorizontalActualDeficitConfigurationPair source.1
  by_cases hdegree : SixVertexLocallyDegreeTwo pair.1.1.1 pair.1.2.1
  · exact .nonNormalizedUnitCharge hdegree
      (sixVertexHorizontalDegreeTwoUnitCharge_of_not_highCharge source.1
        hdegree source.2.2)
  · exact .nonDegreeTwo hdegree


noncomputable def sixVertexHorizontalDegreeTwoHallSourcePhysicalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :
    SixVertexHorizontalDegreeTwoHallSource T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexConfigurationPhysicalSource T middle
        hmiddle_pos hmiddle_lt where
  toFun source :=
    (sixVertexHorizontalActualDeficitConfigurationPair source).1
  inj' := by
    intro first second heq
    apply sixVertexHorizontalActualDeficitConfigurationPair_injective
    apply Subtype.ext
    exact heq


noncomputable def sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :
    SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade ↪
      SixVertexConfigurationPhysicalTarget T middle where
  toFun target :=
    (sixVertexHorizontalActualSurplusConfigurationPair target).1
  inj' := by
    intro first second heq
    apply sixVertexHorizontalActualSurplusConfigurationPair_injective
    apply Subtype.ext
    exact heq


end
end StatMech.FrontierD
