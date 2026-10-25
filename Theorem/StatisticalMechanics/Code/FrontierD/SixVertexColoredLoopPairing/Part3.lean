/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing


namespace StatMech.FrontierD

noncomputable section

theorem FKColoredLoopPairing.incoming_bondMate
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    (!colored.incoming (fkMedialBondMate T d)) = colored.incoming d := by
  have hcolor := fkMedialCheckerColor_bondMate_ne T d
  unfold incoming
  rw [show colored.color (fkMedialBondMate T d) = colored.color d by
    exact colored.color_bondMate d]
  generalize hc : fkMedialCheckerColor d = c at hcolor ⊢
  generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hcolor ⊢
  generalize hm : colored.color d = m
  cases c <;> cases b <;> cases m <;> simp_all

theorem FKColoredLoopPairing.incoming_localMate_ne
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    colored.incoming (fkMedialLocalMate colored.pairing d) ≠
      colored.incoming d := by
  have hcolor := fkMedialCheckerColor_localMate_ne colored.pairing d
  unfold incoming
  rw [show colored.color (fkMedialLocalMate colored.pairing d) =
      colored.color d by exact colored.color_localMate d]
  generalize hc : fkMedialCheckerColor d = c at hcolor ⊢
  generalize hm : fkMedialCheckerColor
    (fkMedialLocalMate colored.pairing d) = m at hcolor ⊢
  generalize hb : colored.color d = b
  cases c <;> cases m <;> cases b <;> simp_all

theorem FKColoredLoopPairing.dartIncoming_arrows
    {T : EvenTorus} (colored : FKColoredLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialDartIncoming colored.arrows d = colored.incoming d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp only [fkMedialDartIncoming, fkLoopWestIncoming, arrows]
    exact colored.incoming_bondMate ((i, j), .west)
  · simp [fkMedialDartIncoming, fkLoopEastIncoming, arrows]
  · simp only [fkMedialDartIncoming, fkLoopSouthIncoming, arrows]
    exact colored.incoming_bondMate ((i, j), .south)
  · simp [fkMedialDartIncoming, fkLoopNorthIncoming, arrows]

theorem FKColoredLoopPairing.compatible
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    ∀ v, fkLoopPairingCompatible (colored.pairing v)
      colored.arrows v := by
  intro v
  cases hp : colored.pairing v
  · constructor
    · change fkMedialDartIncoming colored.arrows (v, .west) ≠
        fkMedialDartIncoming colored.arrows (v, .north)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .west)).symm
    · change fkMedialDartIncoming colored.arrows (v, .east) ≠
        fkMedialDartIncoming colored.arrows (v, .south)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .east)).symm
  · constructor
    · change fkMedialDartIncoming colored.arrows (v, .west) ≠
        fkMedialDartIncoming colored.arrows (v, .south)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .west)).symm
    · change fkMedialDartIncoming colored.arrows (v, .east) ≠
        fkMedialDartIncoming colored.arrows (v, .north)
      rw [colored.dartIncoming_arrows, colored.dartIncoming_arrows]
      simpa [fkMedialLocalMate, hp] using
        (colored.incoming_localMate_ne (v, .east)).symm

theorem FKColoredLoopPairing.iceRule
    {T : EvenTorus} (colored : FKColoredLoopPairing T) :
    colored.arrows.IceRule := by
  intro v
  exact incomingCount_eq_two_of_fkLoopPairingCompatible
    (colored.pairing v) colored.arrows v (colored.compatible v)

theorem FKColoredLoopPairing.cType_iff_color_west_eq_east
    {T : EvenTorus} (colored : FKColoredLoopPairing T) (v : T.Vertex) :
    colored.arrows.IsCType v ↔
      colored.color (v, .west) = colored.color (v, .east) := by
  rw [sixVertexIsCType_iff_horizontalIncoming_eq]
  rw [show fkLoopWestIncoming colored.arrows v =
      colored.incoming (v, .west) by
    exact colored.dartIncoming_arrows (v, .west),
    show fkLoopEastIncoming colored.arrows v =
      colored.incoming (v, .east) by
    exact colored.dartIncoming_arrows (v, .east)]
  unfold incoming
  have hc : fkMedialCheckerColor (v, FKMedialSide.west) =
      fkMedialCheckerColor (v, FKMedialSide.east) := rfl
  generalize hw : colored.color (v, FKMedialSide.west) = w
  generalize he : colored.color (v, FKMedialSide.east) = e
  generalize hcw : fkMedialCheckerColor (v, FKMedialSide.west) = cw at hc ⊢
  generalize hce : fkMedialCheckerColor (v, FKMedialSide.east) = ce at hc ⊢
  cases w <;> cases e <;> cases cw <;> cases ce <;> simp_all


end
end StatMech.FrontierD
