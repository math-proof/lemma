/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_tail
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).tail =
      (sixVertexTorusEdgeOutgoingDart omega edge).1 := by
  rcases edge with ⟨direction, ⟨column, row⟩⟩
  fin_cases direction <;>
    cases hh : omega.horizontal (column, row) <;>
    cases hv : omega.vertical (column, row) <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.tail,
      sixVertexTorusEdgeOutgoingDart, hh, hv]

@[simp] theorem sixVertexDirectedTorusEdgeOfArrow_head
    {T : EvenTorus} (omega : SixVertexArrows T)
    (edge : SixVertexTorusEdge T) :
    (sixVertexDirectedTorusEdgeOfArrow omega edge).head =
      (sixVertexTorusDartBondMate T
        (sixVertexTorusEdgeOutgoingDart omega edge)).1 := by
  rcases edge with ⟨direction, ⟨column, row⟩⟩
  fin_cases direction <;>
    cases hh : omega.horizontal (column, row) <;>
    cases hv : omega.vertical (column, row) <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.head,
      sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartBondMate, hh, hv,
      svCyclicPred_finitePeriodicSucc]


theorem sixVertexDirectedTorusEdgeOfArrow_physical_injective
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Function.Injective
      (fun edge : SixVertexTorusEdge T =>
        (sixVertexDirectedTorusEdgeOfArrow omega edge).physical) := by
  intro first second heq
  rcases first with ⟨firstDirection, firstVertex⟩
  rcases second with ⟨secondDirection, secondVertex⟩
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    simp [sixVertexDirectedTorusEdgeOfArrow,
      SixVertexDirectedTorusEdge.physical] at heq ⊢ <;>
    exact heq


end
end StatMech.FrontierD
