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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part27


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareLoopGraph_adj_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hxy : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
    fkIsingSquareCarrierOddClass n x ↔
      ¬ fkIsingSquareCarrierOddClass n y := by
  cases x with
  | source =>
      rw [fkIsingSquareLoopGraph_adj_source_iff] at hxy
      subst y
      simp [fkIsingSquareCarrierOddClass,
        fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
  | terminal =>
      rw [fkIsingSquareLoopGraph_adj_terminal_iff] at hxy
      subst y
      simp [fkIsingSquareCarrierOddClass,
        fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
  | dart d =>
      rw [fkIsingSquareLoopGraph_adj_dart_iff] at hxy
      rcases hxy with rfl | hbond
      · simp only [fkIsingSquareCarrierOddClass]
        have hnturn := fkIsingSquare_localMate_cornerTurn_ne n omega d
        cases hd : (fkIsingSquareSideCorner d.2).2 <;>
          cases hm : (fkIsingSquareSideCorner
            (FKIsingMedialDart.localMate omega d).2).2 <;> simp_all
      · cases hy : fkIsingSquareCutBondMate n hn (.dart d) with
        | source =>
            rw [hy] at hbond
            subst y
            have hh := congrArg (fkIsingSquareCutBondMate n hn) hy
            rw [fkIsingSquareCutBondMate_involutive] at hh
            simp [fkIsingSquareCutBondMate] at hh
            subst d
            simp [fkIsingSquareCarrierOddClass,
              fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
        | terminal =>
            rw [hy] at hbond
            subst y
            have hh := congrArg (fkIsingSquareCutBondMate n hn) hy
            rw [fkIsingSquareCutBondMate_involutive] at hh
            simp [fkIsingSquareCutBondMate] at hh
            subst d
            simp [fkIsingSquareCarrierOddClass,
              fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
        | dart f =>
            rw [hy] at hbond
            subst y
            simp only [fkIsingSquareCarrierOddClass]
            have hnturn := fkIsingSquareCutBondMate_dart_cornerTurn_ne
              n hn d f hy
            cases hd : (fkIsingSquareSideCorner d.2).2 <;>
              cases hf : (fkIsingSquareSideCorner f.2).2 <;> simp_all

theorem fkIsingSquareLoopGraph_source_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).degree .source = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset .source =
      {.dart (fkIsingSquareSourceInteriorDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareLoopGraph_adj_source_iff]
  rw [hfin]
  simp

theorem fkIsingSquareLoopGraph_terminal_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).degree .terminal = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset .terminal =
      {.dart (fkIsingSquareTerminalInteriorDart n hn)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareLoopGraph_adj_terminal_iff]
  rw [hfin]
  simp

theorem fkIsingSquareLoopGraph_dart_degree (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareLoopGraph n hn omega).degree (.dart d) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin : (fkIsingSquareLoopGraph n hn omega).neighborFinset (.dart d) =
      {.dart (FKIsingMedialDart.localMate omega d),
        fkIsingSquareCutBondMate n hn (.dart d)} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fkIsingSquareLoopGraph_adj_dart_iff n hn omega d z
  rw [hfin]
  exact Finset.card_pair
    (fkIsingSquareCutBondMate_ne_localMate n hn omega d).symm


theorem fkIsingSquareLoopGraph_source_reachable_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareLoopGraph n hn omega).Reachable .source .terminal := by
  apply jeb_two_odd_reachable_fin (fkIsingSquareLoopGraph n hn omega)
  · rw [fkIsingSquareLoopGraph_source_degree]
    exact odd_one
  · rw [fkIsingSquareLoopGraph_terminal_degree]
    exact odd_one
  · intro z hsource hterminal
    cases z with
    | source => exact False.elim (hsource rfl)
    | terminal => exact False.elim (hterminal rfl)
    | dart d =>
        rw [fkIsingSquareLoopGraph_dart_degree]
        exact even_two


end
end StatMech.Universality
