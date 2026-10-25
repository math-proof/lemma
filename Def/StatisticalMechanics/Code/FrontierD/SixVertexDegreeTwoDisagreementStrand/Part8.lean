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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexOrientedDegreeTwoStrandSuccessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoStrandSuccessor hdegree).subtypePerm fun d => by
    rw [sixVertexDegreeTwoStrandSuccessor_incoming homega heta hdegree]

end
end StatMech.FrontierD
