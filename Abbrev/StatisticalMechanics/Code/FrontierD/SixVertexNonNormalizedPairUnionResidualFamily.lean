module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
public import Instance.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexNonNormalizedUnitChargeResidualSources
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) :=
  {source : SixVertexPositiveUnitComponentResidualGeometricSources T middle
      hmiddle_pos hmiddle_lt grade //
    SixVertexLocallyDegreeTwo
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.1.1
      (sixVertexHorizontalActualDeficitConfigurationPair source.1).1.2.1}


end
end StatMech.FrontierD
