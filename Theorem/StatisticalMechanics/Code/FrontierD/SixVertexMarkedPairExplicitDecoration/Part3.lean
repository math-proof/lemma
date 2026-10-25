/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPreferredCompatiblePairing_compatible
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex) :
    fkLoopPairingCompatible
      (sixVertexPreferredCompatiblePairing omega v) omega v := by
  unfold sixVertexPreferredCompatiblePairing
  split
  · assumption
  · rename_i hfalse
    have hi := homega v
    generalize hw : omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hi hfalse ⊢
    generalize he : omega.horizontal v = e at hi hfalse ⊢
    generalize hs : omega.vertical
      (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hi hfalse ⊢
    generalize hn : omega.vertical v = n at hi hfalse ⊢
    cases w <;> cases e <;> cases s <;> cases n <;>
      simp [fkLoopPairingCompatible, SixVertexArrows.incomingCount,
        fkLoopWestIncoming, fkLoopEastIncoming,
        fkLoopSouthIncoming, fkLoopNorthIncoming,
        hw, he, hs, hn] at hi hfalse ⊢


end
end StatMech.FrontierD
