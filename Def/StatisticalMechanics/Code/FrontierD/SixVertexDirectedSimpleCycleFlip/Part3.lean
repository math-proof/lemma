/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexAtMostTwoCycleFamily.twoCycles
    {T : EvenTorus} (first second : SixVertexDirectedSimpleCycle T)
    (hdisjoint : forall a b,
      (first.edge a).tail != (second.edge b).tail) :
    SixVertexAtMostTwoCycleFamily T where
  count := 2
  count_le_two := by omega
  cycle := ![first, second]
  tail_disjoint := by
    intro i j hne a b
    fin_cases i <;> fin_cases j
    · simp at hne
    · exact hdisjoint a b
    · simpa [bne_comm] using hdisjoint b a
    · simp at hne

end
end StatMech.FrontierD
