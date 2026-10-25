/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexTorusDartEdge_outgoingDart
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusDartEdge T (sixVertexTorusEdgeOutgoingDart omega e) = e := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir <;> cases h : omega.horizontal (i, j) <;>
    cases hv : omega.vertical (i, j) <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, h, hv,
      svCyclicPred_finitePeriodicSucc]

@[simp] theorem sixVertexTorusEdgeOutgoingDart_incoming
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexLocalIncomingPattern omega
        (sixVertexTorusEdgeOutgoingDart omega e).1
        (sixVertexTorusEdgeOutgoingDart omega e).2 = false := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir <;> cases h : omega.horizontal (i, j) <;>
    cases hv : omega.vertical (i, j) <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, h, hv, svCyclicPred_finitePeriodicSucc]


theorem sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
    {T : EvenTorus} (omega : SixVertexArrows T)
    (d : SixVertexTorusDart T)
    (hout : sixVertexLocalIncomingPattern omega d.1 d.2 = false) :
    sixVertexTorusEdgeOutgoingDart omega
      (sixVertexTorusDartEdge T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, finitePeriodicSucc_cyclicPred,
      svCyclicPred_finitePeriodicSucc] at hout ⊢ <;>
    exact hout


end
end StatMech.FrontierD
