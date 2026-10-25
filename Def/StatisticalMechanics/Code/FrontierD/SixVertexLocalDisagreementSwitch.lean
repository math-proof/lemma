/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexLocalIncomingCount
    (p : SixVertexLocalIncomingPattern) : Nat :=
  ∑ i, (p i).toNat

def SixVertexLocalIncomingPattern.Ice
    (p : SixVertexLocalIncomingPattern) : Prop :=
  sixVertexLocalIncomingCount p = 2


def SixVertexLocalIncomingPattern.IsCType
    (p : SixVertexLocalIncomingPattern) : Prop :=
  (p 0).toNat + (p 1).toNat = 0 \/
    (p 0).toNat + (p 1).toNat = 2

end
end StatMech.FrontierD
