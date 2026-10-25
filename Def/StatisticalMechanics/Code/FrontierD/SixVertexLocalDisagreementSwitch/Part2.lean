/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexLocalCTypeCount
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  (if p.IsCType then 1 else 0) + (if q.IsCType then 1 else 0)


def sixVertexLocalSwapTwo
    (p q : SixVertexLocalIncomingPattern) (d e : Fin 4) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun i => if i = d \/ i = e then q i else p i,
    fun i => if i = d \/ i = e then p i else q i)


end
end StatMech.FrontierD
