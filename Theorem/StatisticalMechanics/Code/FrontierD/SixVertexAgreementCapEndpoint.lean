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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwo_agreement_followed_head
    (edge : SixVertexDirectedTorusEdge sixVertexFourByTwoTorus)
    (hfollows : edge.Follows sixVertexFourByTwoLowArrows)
    (hagrees : edge.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    edge.head = sixVertexFourByTwoAgreementSuccessor edge.tail := by
  rcases edge with ⟨⟨x, y⟩, positive⟩ | ⟨⟨x, y⟩, positive⟩ <;>
    fin_cases x <;> fin_cases y <;> cases positive
  all_goals simp_all [SixVertexDirectedTorusEdge.Follows,
      SixVertexDirectedTorusEdge.IsAgreement,
      SixVertexDirectedTorusEdge.head, SixVertexDirectedTorusEdge.tail,
      sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows,
      sixVertexFourByTwoAgreementSuccessor,
      SixVertexArrows.cyclicPred, finitePeriodicSucc,
      sixVertexFourByTwoTorus]


theorem SixVertexDirectedSimpleArc.agreement_tail_next
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (i : Fin (cap.length - 1)) :
    (cap.edge ⟨i.val + 1, by omega⟩).tail =
      sixVertexFourByTwoAgreementSuccessor
        (cap.edge ⟨i.val, by omega⟩).tail := by
  rw [← cap.head_eq_next_tail i]
  exact sixVertexFourByTwo_agreement_followed_head
    (cap.edge ⟨i.val, by omega⟩)
    (hfollows ⟨i.val, by omega⟩)
    (hagrees ⟨i.val, by omega⟩)


end
end StatMech.FrontierD
