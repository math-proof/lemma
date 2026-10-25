/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredIncidenceMate_ne_transitionMate
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    fkIsingSquareWiredIncidenceMate n x ≠
      fkIsingSquareWiredTransitionMate n hn omega x := by
  cases x with
  | source => exact False.elim (hsource rfl)
  | terminal => exact False.elim (hterminal rfl)
  | dart d => simp [fkIsingSquareWiredIncidenceMate,
      fkIsingSquareWiredTransitionMate]
  | bond d =>
      simp only [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredTransitionMate]
      split_ifs <;> simp

@[simp] theorem fkIsingSquareWiredLoopGraph_adj_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredLoopGraph n hn omega).Adj .source z ↔
      z = .bond (fkIsingSquareWiredSourceDart n hn) := by
  simp [fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionMate]

@[simp] theorem fkIsingSquareWiredLoopGraph_adj_terminal_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredLoopGraph n hn omega).Adj .terminal z ↔
      z = .bond (fkIsingSquareWiredTerminalDart n hn) := by
  simp [fkIsingSquareWiredLoopGraph, fkIsingSquareWiredTransitionMate]

theorem fkIsingSquareWiredLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree .source = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset .source =
        {.bond (fkIsingSquareWiredSourceDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp
  rw [hfin]
  simp

theorem fkIsingSquareWiredLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree .terminal = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset .terminal =
        {.bond (fkIsingSquareWiredTerminalDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp
  rw [hfin]
  simp

theorem fkIsingSquareWiredLoopGraph_internal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    (fkIsingSquareWiredLoopGraph n hn omega).degree x = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset x =
      {fkIsingSquareWiredIncidenceMate n x,
        fkIsingSquareWiredTransitionMate n hn omega x} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    change ((x ≠ .source ∧ x ≠ .terminal ∧
        z = fkIsingSquareWiredIncidenceMate n x) ∨
      z = fkIsingSquareWiredTransitionMate n hn omega x) ↔ _
    simp [hsource, hterminal, eq_comm]
  rw [hfin]
  exact Finset.card_pair
    (fkIsingSquareWiredIncidenceMate_ne_transitionMate
      n hn omega x hsource hterminal)


theorem fkIsingSquareWiredLoopGraph_source_reachable_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source .terminal := by
  apply jeb_two_odd_reachable_fin (fkIsingSquareWiredLoopGraph n hn omega)
  · rw [fkIsingSquareWiredLoopGraph_source_degree]
    exact odd_one
  · rw [fkIsingSquareWiredLoopGraph_terminal_degree]
    exact odd_one
  · intro z hsource hterminal
    rw [fkIsingSquareWiredLoopGraph_internal_degree n hn omega z
      hsource hterminal]
    exact even_two


end
end StatMech.Universality
