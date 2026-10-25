/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part4


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalResidualHighGeometricSurplusRepair

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoHighChargeSources T middle
    hmiddle_pos hmiddle_lt grade}


theorem target_supported
    (repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source)
    (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1 (repair.target branch) := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair source.1).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      (repair.target branch)).1
  rw [repair.target_physical]
  simpa using sixVertexHorizontalDegreeTwoLoopSpliceTarget_supported
    (sixVertexHorizontalHallSourceCanonicalLoop source.1)
    (sixVertexHorizontalResidualHighBranchKey source repair.single branch)


theorem target_distinct
    (repair : SixVertexHorizontalResidualHighGeometricSurplusRepair source) :
    repair.target false ≠ repair.target true := by
  intro heq
  apply repair.target_arrows_ne
  have hpair := congrArg
    (fun target =>
      (sixVertexHorizontalActualSurplusConfigurationPair target).1) heq
  change
    (sixVertexHorizontalActualSurplusConfigurationPair
        (repair.target false)).1 =
      (sixVertexHorizontalActualSurplusConfigurationPair
        (repair.target true)).1 at hpair
  rw [repair.target_physical false,
    repair.target_physical true] at hpair
  have hphysical := congrArg
    (fun pair : SixVertexConfigurationPhysicalTarget T middle => pair.1.1)
    hpair
  have hbranch :
      ((sixVertexHorizontalResidualHighBranchKey source repair.single false).splice.target
        false).arrows =
      ((sixVertexHorizontalResidualHighBranchKey source repair.single true).splice.target
        false).arrows := by
    simpa only [sixVertexHorizontalDegreeTwoLoopSpliceTarget_val,
      sixVertexLoopDecoratedSpliceUnitTarget_colored] using hphysical
  simpa [sixVertexHorizontalResidualHighBranchKey,
    FKColoredFineTwoCycleUnitTransferSpliceKey.paired] using hbranch

end SixVertexHorizontalResidualHighGeometricSurplusRepair
end
end StatMech.FrontierD
