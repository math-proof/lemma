/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence
open Finset Matrix


namespace StatMech.FrontierD

theorem incomingCount_eq_two_of_fkLoopPairingCompatible
    (pairing : Bool) (omega : SixVertexArrows T) (v : T.Vertex)
    (h : fkLoopPairingCompatible pairing omega v) :
    omega.incomingCount v = 2 := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at h ⊢
  generalize he : omega.horizontal v = e at h ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at h ⊢
  generalize hn : omega.vertical v = n at h ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkLoopPairingCompatible, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      SixVertexArrows.incomingCount, hw, he, hs, hn] at h ⊢


end StatMech.FrontierD
