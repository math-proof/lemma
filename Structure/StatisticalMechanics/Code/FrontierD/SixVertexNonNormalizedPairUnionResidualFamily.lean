/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily


namespace StatMech.FrontierD

noncomputable section

structure SixVertexNonNormalizedPairUnionPhysicalTargetFamily
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  target :
    (SixVertexNonNormalizedUnitChargeResidualSources T middle
        hmiddle_pos hmiddle_lt grade × Bool) ↪
      {pair : SixVertexConfigurationPhysicalTarget T middle //
        sixVertexConfigurationPairBigrade pair = grade}
  related : ∀ source branch,
    SixVertexConfigurationPairTwoCycleFineRelated
      (sixVertexHorizontalActualDeficitConfigurationPair source.1.1).1
      (target (source, branch)).1
  oldSourceWeight_eq_zero : ∀ source branch,
    sixVertexHorizontalPairProfileChooseWeight
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt)
        (sixVertexHorizontalPairCompletionProfile T
          ((target (source, branch)).1.1.1.horizontal,
            (target (source, branch)).1.2.1.horizontal)) = 0

end
end StatMech.FrontierD
