/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoBottomHorizontalCycle :
    SixVertexDirectedSimpleCycle sixVertexFourByTwoTorus where
  length := 4
  length_pos := by norm_num
  edge i := .horizontal (sixVertexFourByTwoVertex i 0) true
  head_eq_next_tail := by
    intro i
    fin_cases i <;>
      norm_num [SixVertexDirectedTorusEdge.head,
        SixVertexDirectedTorusEdge.tail, sixVertexFourByTwoVertex,
        finitePeriodicSucc, sixVertexFourByTwoTorus]
  tail_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.tail,
        sixVertexFourByTwoVertex]
  physical_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByTwoVertex]

def sixVertexFourByTwoBottomCycleFamily :
    SixVertexAtMostTwoCycleFamily sixVertexFourByTwoTorus where
  count := 1
  count_le_two := by norm_num
  cycle _ := sixVertexFourByTwoBottomHorizontalCycle
  tail_disjoint := by
    intro i j hij
    fin_cases i
    fin_cases j
    simp at hij

end
end StatMech.FrontierD
