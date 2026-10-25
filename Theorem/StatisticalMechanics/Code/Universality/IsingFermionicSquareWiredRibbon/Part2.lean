/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part2
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredCarrierColor_completedIncidence_ne
    (n : Nat) (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredCompletedIncidenceEquiv n x) ≠
      fkIsingSquareWiredCarrierColor n x := by
  cases x with
  | source => simp [fkIsingSquareWiredCompletedIncidenceEquiv,
      fkIsingSquareWiredCarrierColor]
  | terminal => simp [fkIsingSquareWiredCompletedIncidenceEquiv,
      fkIsingSquareWiredCarrierColor]
  | dart d =>
      rcases d with ⟨e, side⟩
      cases side <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
        fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor,
        fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner]
  | bond d =>
      rcases d with ⟨e, side⟩
      cases side <;> simp [fkIsingSquareWiredCompletedIncidenceEquiv,
        fkIsingSquareWiredCarrierColor, fkIsingSquareWiredDartSideColor,
        fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner]

theorem fkIsingSquareWiredCarrierColor_transition_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionEquiv n hn omega x) ≠
      fkIsingSquareWiredCarrierColor n x := by
  cases x with
  | source =>
      simp [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
        fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareWiredTurnColor]
  | terminal =>
      have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      change fkIsingSquareWiredCarrierColor n
          (fkIsingSquareWiredTransitionMate n hn omega .terminal) ≠
        fkIsingSquareWiredCarrierColor n .terminal
      simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
      simp [fkIsingSquareWiredCarrierColor,
        fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareWiredTurnColor]
  | dart d =>
      simpa [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor] using
        fkIsingSquareWiredDartColor_localMate_ne n omega d
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · subst d
        simp [fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
          fkIsingSquareWiredTurnColor]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        have hne := (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
        change fkIsingSquareWiredCarrierColor n
            (fkIsingSquareWiredTransitionMate n hn omega
              (.bond (fkIsingSquareWiredTerminalDart n hn))) ≠
          fkIsingSquareWiredCarrierColor n
            (.bond (fkIsingSquareWiredTerminalDart n hn))
        simp only [fkIsingSquareWiredTransitionMate, hne, ↓reduceIte]
        simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTerminalDart, fkIsingSquareWiredBoundaryDart,
          fkIsingSquareWiredTurnColor]
      · simpa [fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCarrierColor,
          ha, hb] using fkIsingSquareWiredBondColor_bondMate_ne n hn d


end
end StatMech.Universality
