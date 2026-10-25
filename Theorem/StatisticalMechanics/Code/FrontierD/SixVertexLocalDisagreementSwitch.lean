/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalDisagreementSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem exists_sixVertexLocalSwapTwo_of_disagreement
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice) (hd : p d ≠ q d)
    (hnotCC : Not (p.IsCType /\ q.IsCType)) :
    exists e : Fin 4,
      e ≠ d /\ p e ≠ q e /\
      (sixVertexLocalSwapTwo p q d e).1.Ice /\
      (sixVertexLocalSwapTwo p q d e).2.Ice /\
      sixVertexLocalCTypeCount p q <=
        sixVertexLocalCTypeCount
          (sixVertexLocalSwapTwo p q d e).1
          (sixVertexLocalSwapTwo p q d e).2 := by
  decide +revert


theorem sixVertexLocal_all_disagree_of_ice_cType
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hpc : p.IsCType) (hqc : q.IsCType) (hd : p d ≠ q d) :
    forall i : Fin 4, p i ≠ q i := by
  decide +revert


end
end StatMech.FrontierD
