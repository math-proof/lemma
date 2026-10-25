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
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareCutBondMate_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareCutBondMate n hn .source =
      .dart (fkIsingSquareSourceInteriorDart n hn) := rfl

@[simp] theorem fkIsingSquareCutBondMate_terminal
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCutBondMate n hn .terminal =
      .dart (fkIsingSquareTerminalInteriorDart n hn) := rfl

theorem fkIsingSquareLoopGraph_source_adj (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Adj .source
      (.dart (fkIsingSquareSourceInteriorDart n hn)) := by
  exact Or.inr rfl

theorem fkIsingSquareLoopGraph_terminal_adj (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Adj .terminal
      (.dart (fkIsingSquareTerminalInteriorDart n hn)) := by
  exact Or.inr rfl

theorem fkIsingSquareLoopGraph_adj_source_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj .source z ↔
      z = .dart (fkIsingSquareSourceInteriorDart n hn) := by
  change ((∃ d, (.source : FKIsingSquareMedialCarrier n) = .dart d ∧
      z = .dart (FKIsingMedialDart.localMate omega d)) ∨
      z = fkIsingSquareCutBondMate n hn .source) ↔ _
  simp [fkIsingSquareCutBondMate]

theorem fkIsingSquareLoopGraph_adj_terminal_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj .terminal z ↔
      z = .dart (fkIsingSquareTerminalInteriorDart n hn) := by
  change ((∃ d, (.terminal : FKIsingSquareMedialCarrier n) = .dart d ∧
      z = .dart (FKIsingMedialDart.localMate omega d)) ∨
      z = fkIsingSquareCutBondMate n hn .terminal) ↔ _
  simp [fkIsingSquareCutBondMate]

theorem fkIsingSquareLoopGraph_adj_dart_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareLoopGraph n hn omega).Adj (.dart d) z ↔
      z = .dart (FKIsingMedialDart.localMate omega d) ∨
      z = fkIsingSquareCutBondMate n hn (.dart d) := by
  constructor
  · rintro (⟨e, hde, rfl⟩ | hbond)
    · injection hde with he
      subst e
      exact Or.inl rfl
    · exact Or.inr hbond
  · rintro (rfl | rfl)
    · exact Or.inl ⟨d, rfl, rfl⟩
    · exact Or.inr rfl


end
end StatMech.Universality
