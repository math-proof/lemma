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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFourByTwoCanonicalFirstDisagreementArc_start :
    sixVertexFourByTwoCanonicalFirstDisagreementArc.start =
      sixVertexFourByTwoVertex 0 0 := by
  rfl

@[simp] theorem sixVertexFourByTwoCanonicalFirstDisagreementArc_finish :
    sixVertexFourByTwoCanonicalFirstDisagreementArc.finish =
      sixVertexFourByTwoVertex 2 0 := by
  rfl


theorem sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (hstart : cap.start = sixVertexFourByTwoVertex 2 0)
    (hfinish : cap.finish = sixVertexFourByTwoVertex 0 0) :
    exists i : Fin cap.length,
      (cap.edge i).tail = sixVertexFourByTwoVertex 0 1 := by
  have htail0 :
      (cap.edge ⟨0, cap.length_pos⟩).tail =
        sixVertexFourByTwoVertex 2 0 := by
    exact hstart
  have hlengthTwo : 2 <= cap.length := by
    by_contra hnot
    have hpositive := cap.length_pos
    have hlength : cap.length = 1 := by omega
    have hlast : cap.lastIndex = ⟨0, cap.length_pos⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail0] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail1 :
      (cap.edge ⟨1, by omega⟩).tail = sixVertexFourByTwoVertex 1 0 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨0, by omega⟩
    rw [htail0] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  have hlengthThree : 3 <= cap.length := by
    by_contra hnot
    have hlength : cap.length = 2 := by omega
    have hlast : cap.lastIndex = ⟨1, by omega⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail1] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail2 :
      (cap.edge ⟨2, by omega⟩).tail = sixVertexFourByTwoVertex 1 1 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨1, by omega⟩
    rw [htail1] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  have hlengthFour : 4 <= cap.length := by
    by_contra hnot
    have hlength : cap.length = 3 := by omega
    have hlast : cap.lastIndex = ⟨2, by omega⟩ := by
      apply Fin.ext
      simp [SixVertexDirectedSimpleArc.lastIndex, hlength]
    have hhead := sixVertexFourByTwo_agreement_followed_head
      (cap.edge cap.lastIndex) (hfollows cap.lastIndex)
      (hagrees cap.lastIndex)
    change (cap.edge cap.lastIndex).head = sixVertexFourByTwoVertex 0 0 at hfinish
    rw [hfinish, hlast, htail2] at hhead
    norm_num [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] at hhead
  have htail3 :
      (cap.edge ⟨3, by omega⟩).tail = sixVertexFourByTwoVertex 0 1 := by
    have hnext := cap.agreement_tail_next hfollows hagrees
      ⟨2, by omega⟩
    rw [htail2] at hnext
    simpa [sixVertexFourByTwoAgreementSuccessor,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred,
      finitePeriodicSucc, sixVertexFourByTwoTorus] using hnext
  exact ⟨⟨3, by omega⟩, htail3⟩


theorem sixVertexFourByTwo_no_internallyDisjointAgreementCap
    (cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus)
    (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
    (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows)
    (hstart : cap.start = sixVertexFourByTwoCanonicalFirstDisagreementArc.finish)
    (hfinish : cap.finish = sixVertexFourByTwoCanonicalFirstDisagreementArc.start) :
    Not (forall i j,
      (cap.edge i).tail ≠
        (sixVertexFourByTwoCanonicalFirstDisagreementArc.edge j).tail) := by
  intro hdisjoint
  obtain ⟨i, hi⟩ :=
    sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior cap
      hfollows hagrees
      (by simpa using hstart) (by simpa using hfinish)
  apply hdisjoint i ⟨1, by
    change 1 < 4
    norm_num⟩
  simpa [sixVertexFourByTwoCanonicalFirstDisagreementArc,
    SixVertexDirectedTorusEdge.tail, sixVertexFourByTwoVertex,
    finitePeriodicSucc, sixVertexFourByTwoTorus] using hi

end
end StatMech.FrontierD
