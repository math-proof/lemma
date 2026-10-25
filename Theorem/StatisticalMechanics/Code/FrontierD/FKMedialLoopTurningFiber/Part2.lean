/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

theorem modeIncoming_bondMate (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) :
    (!modeIncoming pairing mode (fkMedialBondMate T d)) =
      modeIncoming pairing mode d := by
  have hcomp : (fkMedialLoopGraph T pairing).connectedComponentMk
      (fkMedialBondMate T d) =
      (fkMedialLoopGraph T pairing).connectedComponentMk d := by
    apply SimpleGraph.ConnectedComponent.sound
    exact (show (fkMedialLoopGraph T pairing).Adj
      (fkMedialBondMate T d) d by
        rw [fkMedialLoopGraph_adj_iff]
        right
        rw [fkMedialBondMate_involutive]).reachable
  have hcolor := fkMedialCheckerColor_bondMate_ne T d
  unfold modeIncoming
  rw [hcomp]
  generalize hm : mode ((fkMedialLoopGraph T pairing).connectedComponentMk d) = m
  generalize hc : fkMedialCheckerColor d = c
  generalize hb : fkMedialCheckerColor (fkMedialBondMate T d) = b at hcolor
  cases m <;> cases c <;> cases b <;> simp_all

theorem incoming_arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (d : FKMedialDart T) :
    fkMedialDartIncoming (arrowsOfMode pairing mode) d =
      modeIncoming pairing mode d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · simp only [fkMedialDartIncoming, fkLoopWestIncoming, arrowsOfMode]
    exact modeIncoming_bondMate pairing mode ((i, j), .west)
  · simp [fkMedialDartIncoming, fkLoopEastIncoming, arrowsOfMode]
  · simp only [fkMedialDartIncoming, fkLoopSouthIncoming, arrowsOfMode]
    exact modeIncoming_bondMate pairing mode ((i, j), .south)
  · simp [fkMedialDartIncoming, fkLoopNorthIncoming, arrowsOfMode]

theorem compatible_arrowsOfMode (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    ∀ v, fkLoopPairingCompatible (pairing v)
      (arrowsOfMode pairing mode) v := by
  intro v
  cases hp : pairing v <;>
    simp only [fkLoopPairingCompatible, Bool.false_eq_true,
      ite_false, ite_true]
  · constructor
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .north)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .west) (v, .north) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .west)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .west) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .north) = b at hc ⊢
        cases a <;> cases b <;> simp_all

    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .south)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .east) (v, .south) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .east)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .east) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .south) = b at hc ⊢
        cases a <;> cases b <;> simp_all
  · constructor
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .south)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .west) (v, .south) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .west)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .west) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .south) = b at hc ⊢
        cases a <;> cases b <;> simp_all
    · change fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east) ≠
          fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .north)
      rw [incoming_arrowsOfMode, incoming_arrowsOfMode]
      unfold modeIncoming
      have hcomp := SimpleGraph.ConnectedComponent.sound
        (show (fkMedialLoopGraph T pairing).Adj (v, .east) (v, .north) by
          rw [fkMedialLoopGraph_adj_iff]
          left
          simp [fkMedialLocalMate, hp]).reachable
      rw [hcomp]
      have hc := fkMedialCheckerColor_localMate_ne pairing (v, .east)
      simp [fkMedialLocalMate, hp] at hc
      split
      all_goals
        generalize ha : fkMedialCheckerColor (v, .east) = a at hc ⊢
        generalize hb : fkMedialCheckerColor (v, .north) = b at hc ⊢
        cases a <;> cases b <;> simp_all

theorem eq_iff_eq_of_ne_ne {a b c d : Bool}
    (hab : a ≠ b) (hcd : c ≠ d) : (a = c ↔ b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem incoming_eq_color_iff_reachable
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialDartIncoming a d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming a e = fkMedialCheckerColor e) := by
  obtain ⟨w⟩ := hde
  induction w with
  | nil => exact Iff.rfl
  | @cons d e f hde w ih =>
      exact (eq_iff_eq_of_ne_ne
        (fkMedialLoopGraph_adj_incoming_ne pairing a hcompat hde)
        (fkMedialLoopGraph_adj_checkerColor_ne T pairing hde)).trans ih

end FKMedialTurningFiber
end
end StatMech.FrontierD
