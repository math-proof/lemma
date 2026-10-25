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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoStrandSuccessor_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandSuccessor hdegree d =
      sixVertexDisagreementBondMate
        (sixVertexDegreeTwoLocalMate hdegree d) :=
  rfl

theorem sixVertexDegreeTwoStrandSuccessor_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandSuccessor hdegree d ≠ d := by
  intro hfixed
  have hbond := congrArg sixVertexDisagreementBondMate hfixed
  rw [sixVertexDegreeTwoStrandSuccessor_apply,
    sixVertexDisagreementBondMate_involutive] at hbond
  exact sixVertexDegreeTwoLocalMate_ne_bondMate hdegree d hbond


theorem sixVertexDegreeTwoStrandSuccessor_incoming
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoStrandSuccessor hdegree d).1.1
        (sixVertexDegreeTwoStrandSuccessor hdegree d).1.2 =
      sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
  rw [sixVertexDegreeTwoStrandSuccessor_apply]
  change sixVertexLocalIncomingPattern omega
      (sixVertexTorusDartBondMate T
        (sixVertexDegreeTwoLocalMate hdegree d).1).1
      (sixVertexTorusDartBondMate T
        (sixVertexDegreeTwoLocalMate hdegree d).1).2 = _
  have hlocal := sixVertexDegreeTwoLocalMate_incoming_ne
    homega heta hdegree d
  have hbond := sixVertexLocalIncomingPattern_bondMate_ne omega
    (sixVertexDegreeTwoLocalMate hdegree d).1
  generalize hd : sixVertexLocalIncomingPattern omega d.1.1 d.1.2 = bd at hlocal ⊢
  generalize hl : sixVertexLocalIncomingPattern omega
    (sixVertexDegreeTwoLocalMate hdegree d).1.1
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 = bl at hlocal hbond
  generalize hs : sixVertexLocalIncomingPattern omega
    (sixVertexTorusDartBondMate T
      (sixVertexDegreeTwoLocalMate hdegree d).1).1
    (sixVertexTorusDartBondMate T
      (sixVertexDegreeTwoLocalMate hdegree d).1).2 = bs at hbond ⊢
  cases bd <;> cases bl <;> cases bs <;> simp_all


end
end StatMech.FrontierD
