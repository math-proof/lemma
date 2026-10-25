/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCanonicalFirstDisagreementArc :
    SixVertexDirectedSimpleArc sixVertexFourByTwoTorus where
  length := 4
  length_pos := by norm_num
  edge i :=
    if i.val = 0 then .vertical (sixVertexFourByTwoVertex 0 1) false
    else if i.val = 1 then .horizontal (sixVertexFourByTwoVertex 3 1) false
    else if i.val = 2 then .vertical (sixVertexFourByTwoVertex 3 0) false
    else .horizontal (sixVertexFourByTwoVertex 2 0) false
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
        sixVertexFourByTwoVertex, finitePeriodicSucc,
        sixVertexFourByTwoTorus]
  physical_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [SixVertexDirectedTorusEdge.physical,
        sixVertexFourByTwoVertex]

end
end StatMech.FrontierD
