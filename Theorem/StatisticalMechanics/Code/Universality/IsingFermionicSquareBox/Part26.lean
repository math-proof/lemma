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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part24


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

set_option linter.unusedSimpArgs false in
theorem fkIsingSquareCutBondMate_ne_localMate (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareCutBondMate n hn (.dart d) ≠
      .dart (FKIsingMedialDart.localMate omega d) := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  have hAB : a ≠ b :=
    fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
  have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
  have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
  have hBaB : B a ≠ b :=
    fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
  have hABb : a ≠ B b := by
    intro h
    have hh := congrArg B h
    have hInv := fkIsingSquareBondMate_involutive n hn b
    change B (B b) = b at hInv
    rw [hInv] at hh
    exact hBaB hh
  have hEdge : (B a).1 ≠ (B b).1 :=
    fkIsingSquareBondMate_sourceEdge_ne_terminalEdge n hn
  have hBbBa : B b ≠ B a := by
    intro h
    exact hEdge (congrArg Prod.fst h).symm
  by_cases ha : d = a
  · subst d
    simp [fkIsingSquareCutBondMate, a]
  by_cases hb : d = b
  · subst d
    simp [fkIsingSquareCutBondMate, a, b, hAB.symm]
  by_cases hba : d = B a
  · subst d
    intro h
    simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB, hABb] at h
    have hf := congrArg Prod.fst h
    exact hEdge (by simpa using hf.symm)
  by_cases hbb : d = B b
  · subst d
    intro h
    simp [fkIsingSquareCutBondMate, a, b, B, hBbB, Ne.symm hABb,
      hBbBa, hBaA, hBaB] at h
    have hf := congrArg Prod.fst h
    exact hEdge (by simpa using hf)
  · intro h
    simp [fkIsingSquareCutBondMate, a, b, B, ha, hb, hba, hbb] at h
    exact fkIsingSquareBondMate_ne_localMate n hn omega d h

theorem fkIsingSquareCutBondMate_dart_cornerTurn_ne
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : fkIsingSquareCutBondMate n hn (.dart d) = .dart f) :
    (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  let a := fkIsingSquareSourceInteriorDart n hn
  let b := fkIsingSquareTerminalInteriorDart n hn
  let B := fkIsingSquareBondMate n hn
  by_cases ha : d = a
  · subst d
    simp [fkIsingSquareCutBondMate, a] at h
  by_cases hb : d = b
  · subst d
    have hba' : b ≠ fkIsingSquareSourceInteriorDart n hn := by
      intro h'
      exact fkIsingSquareSourceAttachment_ne_terminalAttachment n hn h'.symm
    simp [fkIsingSquareCutBondMate, b, hba'] at h
  by_cases hba : d = B a
  · have hBaA : B a ≠ a := fkIsingSquareBondMate_ne n hn a
    have hBaB : B a ≠ b :=
      fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment n hn
    rw [show d = B a from hba] at h ⊢
    simp [fkIsingSquareCutBondMate, a, b, B, hBaA, hBaB] at h
    subst f
    have hta := fkIsingSquareBondMate_cornerTurn_ne n hn a
    have htb := fkIsingSquareBondMate_cornerTurn_ne n hn b
    have haT : (fkIsingSquareSideCorner a.2).2 = .counterclockwise := by
      simp [a, fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
    have hbT : (fkIsingSquareSideCorner b.2).2 = .clockwise := by
      simp [b, fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
    rw [haT] at hta
    rw [hbT] at htb
    have hBaT : (fkIsingSquareSideCorner (B a).2).2 = .clockwise := by
      cases h' : (fkIsingSquareSideCorner (B a).2).2
      · exact False.elim (hta (by simpa [B] using h'))
      · rfl
    have hBbT : (fkIsingSquareSideCorner (B b).2).2 = .counterclockwise := by
      cases h' : (fkIsingSquareSideCorner (B b).2).2
      · rfl
      · exact False.elim (htb (by simpa [B] using h'))
    rw [hBaT, hBbT]
    decide
  by_cases hbb : d = B b
  · have hBbB : B b ≠ b := fkIsingSquareBondMate_ne n hn b
    have hBbA : B b ≠ a := by
      intro hba'
      have hh := congrArg B hba'
      rw [show B (B b) = b from
        fkIsingSquareBondMate_involutive n hn b] at hh
      exact fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment
        n hn hh.symm
    have hBbBa : B b ≠ B a := by
      intro hh
      exact fkIsingSquareSourceAttachment_ne_terminalAttachment n hn
        ((fkIsingSquareBondMate_involutive n hn).injective hh.symm)
    rw [show d = B b from hbb] at h ⊢
    simp [fkIsingSquareCutBondMate, a, b, B, hBbA, hBbB, hBbBa] at h
    subst f
    have hta := fkIsingSquareBondMate_cornerTurn_ne n hn a
    have htb := fkIsingSquareBondMate_cornerTurn_ne n hn b
    have haT : (fkIsingSquareSideCorner a.2).2 = .counterclockwise := by
      simp [a, fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
    have hbT : (fkIsingSquareSideCorner b.2).2 = .clockwise := by
      simp [b, fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
    rw [haT] at hta
    rw [hbT] at htb
    have hBaT : (fkIsingSquareSideCorner (B a).2).2 = .clockwise := by
      cases h' : (fkIsingSquareSideCorner (B a).2).2
      · exact False.elim (hta (by simpa [B] using h'))
      · rfl
    have hBbT : (fkIsingSquareSideCorner (B b).2).2 = .counterclockwise := by
      cases h' : (fkIsingSquareSideCorner (B b).2).2
      · rfl
      · exact False.elim (htb (by simpa [B] using h'))
    rw [hBaT, hBbT]
    decide
  · have ha' : d ≠ fkIsingSquareSourceInteriorDart n hn := by
      simpa [a] using ha
    have hb' : d ≠ fkIsingSquareTerminalInteriorDart n hn := by
      simpa [b] using hb
    have hba' : d ≠ fkIsingSquareBondMate n hn
        (fkIsingSquareSourceInteriorDart n hn) := by simpa [a, B] using hba
    have hbb' : d ≠ fkIsingSquareBondMate n hn
        (fkIsingSquareTerminalInteriorDart n hn) := by simpa [b, B] using hbb
    simp [fkIsingSquareCutBondMate, ha', hb', hba', hbb'] at h
    subst f
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d


end
end StatMech.Universality
