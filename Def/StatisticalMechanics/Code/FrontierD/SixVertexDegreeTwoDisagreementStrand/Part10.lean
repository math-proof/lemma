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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexOrientedDisagreementDartEquivEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexOrientedDisagreementDart omega eta ≃
      SixVertexDisagreementEdge omega eta := by
  let toEdge : SixVertexOrientedDisagreementDart omega eta →
      SixVertexDisagreementEdge omega eta := fun d =>
    ⟨sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree d.1).1,
      (sixVertexDegreeTwoLocalMate hdegree d.1).2⟩
  apply Equiv.ofBijective toEdge
  constructor
  · intro a b hab
    have haNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree a.1
    have hbNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree b.1
    have haFalse : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.2 = false := by
      generalize hma : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.2 = ma at haNe ⊢
      rw [a.2] at haNe
      cases ma <;> simp_all
    have hbFalse : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.2 = false := by
      generalize hmb : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.2 = mb at hbNe ⊢
      rw [b.2] at hbNe
      cases mb <;> simp_all
    have haOut := sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
      omega (sixVertexDegreeTwoLocalMate hdegree a.1).1 haFalse
    have hbOut := sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
      omega (sixVertexDegreeTwoLocalMate hdegree b.1).1 hbFalse
    have hmate : sixVertexDegreeTwoLocalMate hdegree a.1 =
        sixVertexDegreeTwoLocalMate hdegree b.1 := by
      have hedge := congrArg
        (fun e : SixVertexDisagreementEdge omega eta => e.1) hab
      change sixVertexTorusDartEdge T
          (sixVertexDegreeTwoLocalMate hdegree a.1).1 =
        sixVertexTorusDartEdge T
          (sixVertexDegreeTwoLocalMate hdegree b.1).1 at hedge
      apply Subtype.ext
      rw [← haOut, ← hbOut]
      exact congrArg (sixVertexTorusEdgeOutgoingDart omega) hedge
    have horiented : a.1 = b.1 := by
      rw [← sixVertexDegreeTwoLocalMate_involutive hdegree a.1,
        ← sixVertexDegreeTwoLocalMate_involutive hdegree b.1,
        hmate]
    exact Subtype.ext horiented
  · intro e
    let outgoing : SixVertexDisagreementDart omega eta :=
      ⟨sixVertexTorusEdgeOutgoingDart omega e.1, by
        rw [sixVertexTorusDartEdge_outgoingDart]
        exact e.2⟩
    have hout : sixVertexLocalIncomingPattern omega
        outgoing.1.1 outgoing.1.2 = false := by
      exact sixVertexTorusEdgeOutgoingDart_incoming omega e.1
    have hmateNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree outgoing
    have hmateTrue : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.1
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.2 = true := by
      generalize hm : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.1
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.2 = m at hmateNe ⊢
      rw [hout] at hmateNe
      cases m <;> simp_all
    let source : SixVertexOrientedDisagreementDart omega eta :=
      ⟨sixVertexDegreeTwoLocalMate hdegree outgoing, hmateTrue⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree source.1).1 = e.1
    rw [show source.1 = sixVertexDegreeTwoLocalMate hdegree outgoing by rfl,
      sixVertexDegreeTwoLocalMate_involutive,
      sixVertexTorusDartEdge_outgoingDart]


def sixVertexTorusEdgeSeamSign
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Int :=
  if e.1 = 1 ∧ e.2.2 = svFinLast T.height_pos then
    (eta.vertical e.2).toNat - (omega.vertical e.2).toNat
  else 0

end
end StatMech.FrontierD
