/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip


namespace StatMech.FrontierD

noncomputable section

def SixVertexAtMostTwoCycleFamily.singletonCycle
    {T : EvenTorus} (cycle : SixVertexDirectedSimpleCycle T) :
    SixVertexAtMostTwoCycleFamily T where
  count := 1
  count_le_two := by omega
  cycle := fun _ => cycle
  tail_disjoint := by
    intro first second hne
    fin_cases first
    fin_cases second
    simp at hne

end
end StatMech.FrontierD
