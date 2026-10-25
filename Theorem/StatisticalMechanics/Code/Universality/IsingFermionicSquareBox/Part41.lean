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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part38


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareLiftedWinding_succ
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i + 1 < (fkIsingSquareExplorationOrder n hn omega).length) :
    fkIsingSquareLiftedWinding n hn omega
        (fkIsingSquareExplorationOrder n hn omega)[i + 1] =
      fkIsingSquareLiftedWinding n hn omega
          (fkIsingSquareExplorationOrder n hn omega)[i] +
        (fkIsingSquarePhysicalTransitionTurn n hn omega
          (fkIsingSquareExplorationOrder n hn omega)[i]
          (fkIsingSquareExplorationOrder n hn omega)[i + 1] : Real) *
            (Real.pi / 4) := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquarePhysicalTransitionTurn]
  rw [fkIsingSquareLiftedTurnCount_succ n hn omega i hi]
  push_cast
  ring

@[simp] theorem fkIsingSquareLiftedWinding_terminal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    fkIsingSquareLiftedWinding n hn omega .terminal = 0 := by
  simp [fkIsingSquareLiftedWinding]

theorem fkIsingSquare_closed_west_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .west) :
    fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .west)) - Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_closed_west_south_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_closed_east_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setClosed e.1 omega) e .east) :
    fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedWinding n hn (setClosed e.1 omega)
        (.dart (e, .east)) - Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_closed_east_north_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_open_west_north_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .west) :
    fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .north)) =
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .west)) + Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_open_west_north_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring

theorem fkIsingSquare_open_east_south_winding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : fkIsingSquarePathUsesLocalSide n hn
      (setOpen e.1 omega) e .east) :
    fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .south)) =
      fkIsingSquareLiftedWinding n hn (setOpen e.1 omega)
        (.dart (e, .east)) + Real.pi / 2 := by
  simp only [fkIsingSquareLiftedWinding,
    fkIsingSquarePhysicalTurnCount,
    fkIsingSquare_open_east_south_turnCount n hn omega e h]
  simp only [fkIsingSquareObservationFrameTurn]
  push_cast
  ring


end
end StatMech.Universality
