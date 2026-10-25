/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part8


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredSourceDart_ne_terminalDart
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareWiredSourceDart n hn ≠
      fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
  cases hi

theorem fkIsingSquareWiredTransitionMate_involutive
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    Function.Involutive (fkIsingSquareWiredTransitionMate n hn omega) := by
  let a := fkIsingSquareWiredSourceDart n hn
  let b := fkIsingSquareWiredTerminalDart n hn
  let B := fkIsingSquareWiredBondMate n hn
  have hab : a ≠ b := fkIsingSquareWiredSourceDart_ne_terminalDart n hn
  have hBa : B a = b := by
    simpa [a, b, B, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredTerminalDart] using
      fkIsingSquareWiredBondMate_bottom n hn
  have hBb : B b = a := by
    simpa [a, b, B, fkIsingSquareWiredSourceDart,
      fkIsingSquareWiredTerminalDart] using
      fkIsingSquareWiredBondMate_top n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareWiredBondMate_involutive n hn
  intro x
  cases x with
  | source => simp [fkIsingSquareWiredTransitionMate, a, b, hab]
  | terminal => simp [fkIsingSquareWiredTransitionMate, a, b, hab.symm]
  | dart d =>
      change FKIsingSquareWiredCarrier.dart
        (FKIsingMedialDart.localMate omega
          (FKIsingMedialDart.localMate omega d)) = .dart d
      rw [FKIsingMedialDart.localMate_involutive]
  | bond d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareWiredTransitionMate, a]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareWiredTransitionMate, a, b, hab.symm]
      · have hBdA : B d ≠ a := by
          intro h
          have hh := congrArg B h
          rw [hInv d, hBa] at hh
          exact hb hh
        have hBdB : B d ≠ b := by
          intro h
          have hh := congrArg B h
          rw [hInv d, hBb] at hh
          exact ha hh
        have hfirst : fkIsingSquareWiredTransitionMate n hn omega (.bond d) =
            .bond (B d) := by
          simp [fkIsingSquareWiredTransitionMate, a, b, B, ha, hb]
        have hsecond : fkIsingSquareWiredTransitionMate n hn omega (.bond (B d)) =
            .bond (B (B d)) := by
          simp [fkIsingSquareWiredTransitionMate, a, b, B, hBdA, hBdB]
        rw [hfirst, hsecond, hInv d]

theorem fkIsingSquareWiredTransitionMate_ne
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredTransitionMate n hn omega x ≠ x := by
  cases x with
  | source => simp [fkIsingSquareWiredTransitionMate]
  | terminal => simp [fkIsingSquareWiredTransitionMate]
  | dart d =>
      simp [fkIsingSquareWiredTransitionMate,
        FKIsingMedialDart.localMate_ne omega d]
  | bond d =>
      by_cases ha : d = fkIsingSquareWiredSourceDart n hn
      · simp [fkIsingSquareWiredTransitionMate, ha]
      by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
      · subst d
        simp [fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredSourceDart_ne_terminalDart n hn |>.symm]
      · simp [fkIsingSquareWiredTransitionMate, ha, hb,
          fkIsingSquareWiredBondMate_ne n hn d]


end
end StatMech.Universality
