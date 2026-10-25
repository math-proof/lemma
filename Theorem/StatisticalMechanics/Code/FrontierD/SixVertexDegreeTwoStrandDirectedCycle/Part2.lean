/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoLocalMate_incoming_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1.1
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1.2 = false := by
  have hne := sixVertexDegreeTwoLocalMate_incoming_ne
    homega heta hdegree dart.1
  rw [dart.2] at hne
  cases h : sixVertexLocalIncomingPattern omega
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1.1
    (sixVertexDegreeTwoLocalMate hdegree dart.1).1.2 <;> simp_all

theorem sixVertexDegreeTwoOrientedStrandEdge_tail
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).tail =
      dart.1.1.1 := by
  rw [sixVertexDegreeTwoOrientedStrandEdge,
    sixVertexDirectedTorusEdgeOfArrow_tail,
    sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1
      (sixVertexDegreeTwoLocalMate_incoming_false
        homega heta hdegree dart)]
  exact sixVertexDegreeTwoLocalMate_vertex hdegree dart.1

theorem sixVertexDegreeTwoOrientedStrandEdge_head
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).head =
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree dart).1.1.1 := by
  rw [sixVertexDegreeTwoOrientedStrandEdge,
    sixVertexDirectedTorusEdgeOfArrow_head,
    sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false omega
      (sixVertexDegreeTwoLocalMate hdegree dart.1).1
      (sixVertexDegreeTwoLocalMate_incoming_false
        homega heta hdegree dart)]
  rfl


theorem sixVertexOrientedDisagreementDart_vertex_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Function.Injective
      (fun dart : SixVertexOrientedDisagreementDart omega eta =>
        dart.1.1.1) := by
  intro first second hvertex
  change first.1.1.1 = second.1.1.1 at hvertex
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hvertex
  · by_contra hside
    have hbits := sixVertexLocalIncoming_ne_at_two_disagreements
      (sixVertexLocalIncomingPattern omega first.1.1.1)
      (sixVertexLocalIncomingPattern eta first.1.1.1)
      first.1.1.2 second.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega first.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta first.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree first.1)
      (sixVertexDisagreementDart_side_mem first.1)
      (by
        simpa only [hvertex] using
          (sixVertexDisagreementDart_side_mem second.1))
      (Ne.symm hside)
    apply hbits
    calc
      sixVertexLocalIncomingPattern omega first.1.1.1 second.1.1.2 =
          sixVertexLocalIncomingPattern omega second.1.1.1 second.1.1.2 := by
        rw [hvertex]
      _ = true := second.2
      _ = sixVertexLocalIncomingPattern omega first.1.1.1 first.1.1.2 :=
        first.2.symm


theorem sixVertexDegreeTwoOrientedStrandEdge_physical_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Function.Injective
      (fun dart : SixVertexOrientedDisagreementDart omega eta =>
        (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).physical) := by
  intro first second heq
  apply (sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree).injective
  apply Subtype.ext
  apply sixVertexDirectedTorusEdgeOfArrow_physical_injective omega
  exact heq


end
end StatMech.FrontierD
