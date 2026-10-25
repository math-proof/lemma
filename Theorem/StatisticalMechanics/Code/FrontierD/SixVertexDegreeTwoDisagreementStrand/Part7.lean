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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexOrientedDegreeTwoStrandSuccessor_val
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree d).1 =
        sixVertexDegreeTwoStrandSuccessor hdegree d.1 :=
  rfl

theorem sixVertexOrientedDegreeTwoStrandSuccessor_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree d ≠ d := by
  intro h
  exact sixVertexDegreeTwoStrandSuccessor_ne hdegree d.1
    (congrArg Subtype.val h)

theorem sixVertexOrientedDegreeTwoStrandSuccessor_support
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).support = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro d
  exact Equiv.Perm.mem_support.mpr
    (sixVertexOrientedDegreeTwoStrandSuccessor_ne
      homega heta hdegree d)


end
end StatMech.FrontierD
