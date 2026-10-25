/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusDartOfMedialDart_bondMate
    (T : EvenTorus) (d : FKMedialDart T) :
    sixVertexTorusDartOfMedialDart (fkMedialBondMate T d) =
      sixVertexTorusDartBondMate T
        (sixVertexTorusDartOfMedialDart d) := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;> rfl

theorem fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (d : FKMedialDart T) :
    (source false).color d = (source true).color d ↔
      sixVertexTorusEdgeArrow (source false).arrows
          (sixVertexTorusDartEdge T
            (sixVertexTorusDartOfMedialDart d)) =
        sixVertexTorusEdgeArrow (source true).arrows
          (sixVertexTorusDartEdge T
            (sixVertexTorusDartOfMedialDart d)) := by
  rcases d with ⟨v, side⟩
  have hfalse := (source false).dartIncoming_arrows (v, side)
  have htrue := (source true).dartIncoming_arrows (v, side)
  calc
    (source false).color (v, side) = (source true).color (v, side) ↔
        (source false).incoming (v, side) =
          (source true).incoming (v, side) := by
      unfold FKColoredLoopPairing.incoming
      generalize hc : fkMedialCheckerColor (v, side) = c
      generalize hf : (source false).color (v, side) = f
      generalize ht : (source true).color (v, side) = t
      cases c <;> cases f <;> cases t <;> simp
    _ ↔ fkMedialDartIncoming (source false).arrows (v, side) =
        fkMedialDartIncoming (source true).arrows (v, side) := by
      rw [hfalse, htrue]
    _ ↔ _ := by
      cases side <;>
        simp [sixVertexTorusDartEdge, sixVertexTorusDartOfMedialDart,
          sixVertexFinSideOfMedialSide, sixVertexTorusIncidentEdge,
          sixVertexTorusEdgeArrow, fkMedialDartIncoming,
          fkLoopWestIncoming, fkLoopEastIncoming,
          fkLoopSouthIncoming, fkLoopNorthIncoming]


end
end StatMech.FrontierD
