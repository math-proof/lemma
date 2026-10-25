/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem card_localCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (v : T.Vertex) :
    Fintype.card
        {pairing : Bool // fkLoopPairingCompatible pairing omega v} =
      if omega.IsCType v then 2 else 1 := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s
  generalize hn : omega.vertical v = n
  have hice := homega v
  cases w <;> cases e <;> cases s <;> cases n <;>
    simp [Fintype.card_subtype, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.IsCType,
      SixVertexArrows.incomingCount, hw, he, hs, hn] at hice ⊢


theorem card_sixVertexCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule) :
    Fintype.card (SixVertexCompatibleLoopPairing omega) =
      2 ^ sixVertexTorusCTypeCount omega := by
  rw [Fintype.card_congr (sixVertexCompatibleLoopPairingEquivPi omega),
    Fintype.card_pi]
  simp_rw [card_localCompatibleLoopPairing omega homega]
  simp_rw [show forall v : T.Vertex,
      (if omega.IsCType v then 2 else 1) =
        2 ^ (if omega.IsCType v then 1 else 0) by
    intro v
    by_cases h : omega.IsCType v <;> simp [h]]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl


end
end StatMech.FrontierD
