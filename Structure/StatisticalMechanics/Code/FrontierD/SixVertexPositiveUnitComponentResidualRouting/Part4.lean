/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part10


namespace StatMech.FrontierD

noncomputable section

structure SixVertexHorizontalResidualHighGeometricSurplusRepair
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
      hmiddle_pos hmiddle_lt grade) where
  single : SixVertexDegreeTwoSynchronizedSupportedSplitTarget
    (sixVertexHorizontalDegreeTwoLoopHighChargeSeed
      (sixVertexHorizontalHallHighSourceCanonicalLoop source))
  target_arrows_ne :
    let key := sixVertexHorizontalResidualHighBaseKey source single
    (key.splice.target false).arrows ≠ (key.splice.target true).arrows
  target : Bool → SixVertexHorizontalDegreeTwoHallTarget T middle
    hmiddle_pos hmiddle_lt grade
  target_physical : ∀ branch,
    (sixVertexHorizontalActualSurplusConfigurationPair (target branch)).1 =
      (sixVertexHorizontalDegreeTwoLoopSpliceTarget
        (sixVertexHorizontalHallSourceCanonicalLoop source.1)
        (sixVertexHorizontalResidualHighBranchKey source single branch)).1.1

end
end StatMech.FrontierD
