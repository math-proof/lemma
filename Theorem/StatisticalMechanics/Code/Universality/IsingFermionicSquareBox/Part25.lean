/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part23


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_involutive (n : Nat) (hn : 0 < n) :
    Function.Involutive (fkIsingSquareCutBondMate n hn) := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareBondMate_involutive n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABa : a ≠ B a := Ne.symm hBaA
  have hBBb : b ≠ B b := Ne.symm hBbB
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    rw [hInv b] at hh
    exact hBaB hh
  have hBbA : B b ≠ a := Ne.symm hABb
  have hBaBb : B a ≠ B b := by
    intro h
    exact hAB (hInv.injective h)
  have hBbBa : B b ≠ B a := Ne.symm hBaBb
  intro x
  cases x with
  | source =>
      simp [fkIsingSquareCutBondMate, a, b, B, hABa, hAB, hBaA, hBaB]
  | terminal =>
      simp [fkIsingSquareCutBondMate, a, b, B, hAB, hAB.symm,
        hBBb, hBbA, hBbB]
  | dart d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hABa, hAB, hBaA, hBaB]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hAB, hAB.symm,
          hBBb, hBbA, hBbB]
      by_cases hba : d = B a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB,
          hBaBb, hBbA, hBbB, hInv]
      by_cases hbb : d = B b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBbB, hBbA,
          hBbBa, hBaA, hBaB, hInv]
      · have hBdA : B d ≠ a := by
          intro h
          apply hba
          have hh := congrArg B h
          rw [hInv d] at hh
          exact hh
        have hBdB : B d ≠ b := by
          intro h
          apply hbb
          have hh := congrArg B h
          rw [hInv d] at hh
          exact hh
        have hBdBa : B d ≠ B a := by
          intro h
          exact ha (hInv.injective h)
        have hBdBb : B d ≠ B b := by
          intro h
          exact hb (hInv.injective h)
        simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb,
          hBdA, hBdB, hBdBa, hBdBb, hInv]
        exact fkIsingSquareBondMate_involutive n hn d

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_ne (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareMedialCarrier n) :
    fkIsingSquareCutBondMate n hn x ≠ x := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hInv : Function.Involutive B := by
    simpa [B] using fkIsingSquareBondMate_involutive n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    rw [hInv b] at hh
    exact hBaB hh
  have hBaBb : B a ≠ B b := by
    intro h
    exact hAB ((fkIsingSquareBondMate_involutive n hn).injective h)
  cases x with
  | source => simp [fkIsingSquareCutBondMate]
  | terminal => simp [fkIsingSquareCutBondMate]
  | dart d =>
      by_cases ha : d = a
      · subst d
        simp [fkIsingSquareCutBondMate, a]
      by_cases hb : d = b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, hAB.symm]
      by_cases hba : d = B a
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB,
          hBaBb, hABb]
        exact Ne.symm hBaBb
      by_cases hbb : d = B b
      · subst d
        simp [fkIsingSquareCutBondMate, a, b, B, hBbB,
          Ne.symm hABb, Ne.symm hBaBb, hBaA, hBaB]
        exact hBaBb
      · simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb,
          fkIsingSquareBondMate_ne n hn d]


end
end StatMech.Universality
