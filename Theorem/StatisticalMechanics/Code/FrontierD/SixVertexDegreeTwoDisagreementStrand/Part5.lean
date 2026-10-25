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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoLocalMate_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.1 = d.1.1 := by
  simp [sixVertexDegreeTwoLocalMate]

theorem sixVertexDegreeTwoLocalMate_involutive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoLocalMate hdegree d) = d := by
  apply Subtype.ext
  apply Prod.ext
  · simp [sixVertexDegreeTwoLocalMate]
  · simp only [sixVertexDegreeTwoLocalMate]
    exact finsetOther_involutive _ _ _ _

theorem sixVertexDegreeTwoLocalMate_side_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 ∈
      sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega d.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1) := by
  simp only [sixVertexDegreeTwoLocalMate]
  apply finsetOther_mem

theorem sixVertexDegreeTwoLocalMate_side_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠ d.1.2 := by
  simp only [sixVertexDegreeTwoLocalMate]
  apply finsetOther_ne

theorem sixVertexDegreeTwoLocalMate_ne_bondMate
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoLocalMate hdegree d ≠
      sixVertexDisagreementBondMate d := by
  intro h
  have hvertex := congrArg (fun e : SixVertexDisagreementDart omega eta =>
    e.1.1) h
  change (sixVertexDegreeTwoLocalMate hdegree d).1.1 =
    (sixVertexDisagreementBondMate d).1.1 at hvertex
  rw [sixVertexDegreeTwoLocalMate_vertex] at hvertex
  exact sixVertexTorusDartBondMate_vertex_ne T d.1 hvertex.symm


theorem sixVertexLocalIncoming_ne_at_two_disagreements
    (p q : SixVertexLocalIncomingPattern) (d e : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hcard : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : d ∈ sixVertexLocalDisagreementSides p q)
    (he : e ∈ sixVertexLocalDisagreementSides p q) (hne : e ≠ d) :
    p e ≠ p d := by
  decide +revert

theorem sixVertexDegreeTwoLocalMate_incoming_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree d).1.1
        (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠
      sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
  rw [sixVertexDegreeTwoLocalMate_vertex]
  exact sixVertexLocalIncoming_ne_at_two_disagreements
    (sixVertexLocalIncomingPattern omega d.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1) d.1.2
    (sixVertexDegreeTwoLocalMate hdegree d).1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d)
    (sixVertexDisagreementDart_side_mem d)
    (sixVertexDegreeTwoLocalMate_side_mem hdegree d)
    (sixVertexDegreeTwoLocalMate_side_ne hdegree d)


theorem sixVertexLocalIncomingPattern_bondMate_ne
    {T : EvenTorus} (omega : SixVertexArrows T)
    (d : SixVertexTorusDart T) :
    sixVertexLocalIncomingPattern omega
        (sixVertexTorusDartBondMate T d).1
        (sixVertexTorusDartBondMate T d).2 ≠
      sixVertexLocalIncomingPattern omega d.1 d.2 := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, svCyclicPred_finitePeriodicSucc]


end
end StatMech.FrontierD
