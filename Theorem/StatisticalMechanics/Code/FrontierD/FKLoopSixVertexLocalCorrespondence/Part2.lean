/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part2
open Finset Matrix


namespace StatMech.FrontierD

theorem sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight
    (lam : Real) (omega : SixVertexArrows T) (v : T.Vertex) :
    (∑ pairing : Bool,
      fkOrientedLoopLocalWeight lam pairing omega v) =
      omega.localWeight
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s
  generalize hn : omega.vertical v = n
  cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkOrientedLoopLocalWeight, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.localWeight,
      SixVertexArrows.incomingCount, SixVertexArrows.IsCType,
      hw, he, hs, hn, add_comm]


end StatMech.FrontierD
