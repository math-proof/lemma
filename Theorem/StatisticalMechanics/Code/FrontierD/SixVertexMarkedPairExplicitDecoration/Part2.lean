/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_cTypeSite
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Fintype.card {v : T.Vertex // omega.IsCType v} =
      sixVertexTorusCTypeCount omega := by
  rw [Fintype.card_subtype]
  unfold sixVertexTorusCTypeCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem card_sixVertexPairCTypeSite
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    Fintype.card (SixVertexPairCTypeSite omega eta) =
      sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta := by
  rw [Fintype.card_congr
      (sixVertexPairCTypeSiteEquivSum omega eta),
    Fintype.card_sum, card_cTypeSite, card_cTypeSite]

theorem fkLoopPairingCompatible_of_cType
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex)
    (hc : omega.IsCType v) (pairing : Bool) :
    fkLoopPairingCompatible pairing omega v := by
  have hi := homega v
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hi hc ⊢
  generalize he : omega.horizontal v = e at hi hc ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hi hc ⊢
  generalize hn : omega.vertical v = n at hi hc ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkLoopPairingCompatible, SixVertexArrows.IsCType,
      SixVertexArrows.incomingCount, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      hw, he, hs, hn] at hi hc ⊢


end
end StatMech.FrontierD
