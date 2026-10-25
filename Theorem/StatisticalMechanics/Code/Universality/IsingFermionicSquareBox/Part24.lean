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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part22


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquare_source_ne_terminal (n : Nat) :
    (FKIsingSquareMedialCarrier.source : FKIsingSquareMedialCarrier n) ≠
      .terminal := by
  simp

theorem fkIsingSquare_sourceAttachment_ne_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareSourceAttachment n hn ≠ .source := by
  simp [fkIsingSquareSourceAttachment]

theorem fkIsingSquare_terminalAttachment_ne_terminal (n : Nat) (hn : 0 < n) :
    fkIsingSquareTerminalAttachment n hn ≠ .terminal := by
  simp [fkIsingSquareTerminalAttachment]

@[simp] theorem fkIsingSquareDartEndpoint_sourceAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareSourcePrimalEdge n hn, .west) =
      fkIsingSquareMarkedA n := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_source]
  rfl

@[simp] theorem fkIsingSquareDartEndpoint_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartEndpoint n
      (fkIsingSquareTerminalPrimalEdge n hn, .north) =
      fkIsingSquareMarkedB n := by
  unfold fkIsingSquareDartEndpoint
  rw [fkIsingSquareOrientedEdge_terminal]
  rfl

theorem fkIsingSquareSourceAttachment_ne_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareSourcePrimalEdge n hn, FKIsingMedialSide.west) ≠
      (fkIsingSquareTerminalPrimalEdge n hn, FKIsingMedialSide.north) := by
  intro h
  have he := congrArg (fkIsingSquareDartEndpoint n) h
  apply fkIsingSquareMarkedA_ne_markedB n hn
  simpa using he

theorem fkIsingSquareBondMate_sourceAttachment_ne_terminalAttachment
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareBondMate n hn
        (fkIsingSquareSourcePrimalEdge n hn, .west) ≠
      (fkIsingSquareTerminalPrimalEdge n hn, .north) := by
  intro h
  have he := congrArg (fkIsingSquareDartEndpoint n) h
  rw [fkIsingSquareDartEndpoint_bondMate,
    fkIsingSquareDartEndpoint_sourceAttachment] at he
  rw [fkIsingSquareDartEndpoint_terminalAttachment] at he
  exact fkIsingSquareMarkedA_ne_markedB n hn he

theorem fkIsingSquareBondMate_sourceEdge_ne_terminalEdge
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareBondMate n hn
      (fkIsingSquareSourcePrimalEdge n hn, .west)).1 ≠
    (fkIsingSquareBondMate n hn
      (fkIsingSquareTerminalPrimalEdge n hn, .north)).1 := by
  intro hedge
  let da := fkIsingSquareBondMate n hn
    (fkIsingSquareSourcePrimalEdge n hn, .west)
  let db := fkIsingSquareBondMate n hn
    (fkIsingSquareTerminalPrimalEdge n hn, .north)
  have haMem : fkIsingSquareMarkedA n ∈ da.1.1 := by
    have hmem := fkIsingSquareDartEndpoint_mem n da
    have hend : fkIsingSquareDartEndpoint n da =
        fkIsingSquareMarkedA n := by
      simp [da]
    rwa [hend] at hmem
  have hbMemDb : fkIsingSquareMarkedB n ∈ db.1.1 := by
    have hmem := fkIsingSquareDartEndpoint_mem n db
    have hend : fkIsingSquareDartEndpoint n db =
        fkIsingSquareMarkedB n := by
      simp [db]
    rwa [hend] at hmem
  have hbMem : fkIsingSquareMarkedB n ∈ da.1.1 := by
    change fkIsingSquareMarkedB n ∈ da.1.1
    rw [hedge]
    exact hbMemDb
  exact fkIsingSquareMarkedA_not_adj_markedB n hn
    (adj_of_mem_edge_of_ne (fkSquareBoxPlanar n).G da.1
      haMem hbMem (fkIsingSquareMarkedA_ne_markedB n hn))

@[simp] theorem fkIsingSquare_localMate_fst
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (FKIsingMedialDart.localMate omega d).1 = d.1 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate, h]

theorem fkIsingSquare_localMate_cornerTurn_ne
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (FKIsingMedialDart.localMate omega d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate, fkIsingSquareSideCorner, h]


end
end StatMech.Universality
