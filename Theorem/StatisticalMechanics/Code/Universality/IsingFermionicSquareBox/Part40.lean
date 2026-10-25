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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part37


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquarePhysicalTransitionTurn_local_table
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .west)) (.dart (e, .south)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .south)) (.dart (e, .west)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .east)) (.dart (e, .north)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setClosed e.1 omega)
      (.dart (e, .north)) (.dart (e, .east)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .west)) (.dart (e, .north)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .north)) (.dart (e, .west)) = -2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .east)) (.dart (e, .south)) = 2) ∧
    (fkIsingSquarePhysicalTransitionTurn n hn (setOpen e.1 omega)
      (.dart (e, .south)) (.dart (e, .east)) = -2) := by
  rcases fkIsingSquareExplorationTransitionTurn_local_table n hn omega e with
    ⟨hWS, hSW, hEN, hNE, hWN, hNW, hES, hSE⟩
  simp only [fkIsingSquarePhysicalTransitionTurn,
    fkIsingSquareObservationFrameTurn, hWS, hSW, hEN, hNE,
    hWN, hNW, hES, hSE]
  omega


end
end StatMech.Universality
