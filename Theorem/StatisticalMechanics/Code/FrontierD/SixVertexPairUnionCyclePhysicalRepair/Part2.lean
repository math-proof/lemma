/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSwapPhysicalTarget_swap
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexSwapPhysicalTarget (sixVertexSwapPhysicalTarget target) =
      target := by
  rfl

theorem sixVertexSwapPhysicalTarget_injective
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexSwapPhysicalTarget (T := T) (middle := middle)) := by
  intro first second heq
  have := congrArg sixVertexSwapPhysicalTarget heq
  simpa using this


end
end StatMech.FrontierD
