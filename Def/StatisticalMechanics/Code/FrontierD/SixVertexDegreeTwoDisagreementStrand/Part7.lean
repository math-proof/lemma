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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexDisagreementBondMateEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    SixVertexDisagreementDart omega eta ≃
      SixVertexDisagreementDart omega eta where
  toFun := sixVertexDisagreementBondMate
  invFun := sixVertexDisagreementBondMate
  left_inv := sixVertexDisagreementBondMate_involutive
  right_inv := sixVertexDisagreementBondMate_involutive


def sixVertexDegreeTwoLocalMateEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexDisagreementDart omega eta ≃
      SixVertexDisagreementDart omega eta where
  toFun := sixVertexDegreeTwoLocalMate hdegree
  invFun := sixVertexDegreeTwoLocalMate hdegree
  left_inv := sixVertexDegreeTwoLocalMate_involutive hdegree
  right_inv := sixVertexDegreeTwoLocalMate_involutive hdegree


def sixVertexDegreeTwoStrandSuccessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (SixVertexDisagreementDart omega eta) :=
  (sixVertexDegreeTwoLocalMateEquiv hdegree).trans
    sixVertexDisagreementBondMateEquiv

end
end StatMech.FrontierD
