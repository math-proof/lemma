/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

noncomputable def hexagonalInnerKappa (n : Nat) (beta0 : Real) : Real :=
  (reindexedOpenIncidentEdges
    (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n))
    (hexagonalBoxEndU n) (hexagonalBoxEndV n) (hexagonalBoxRoot n)).prod
      (fun _ => Real.exp (-beta0))

def hexagonalBoxNeighbor (n : Nat) (hn : 1 ≤ n) (i : Fin 3) :
    HexagonalBoxVertex n :=
  ⟨hexagonalNeighbor (0, false) i, ⟨by
    fin_cases i <;> intro j <;> fin_cases j <;>
      simp [hexagonalNeighbor, hexagonalStep] <;> omega,
    Set.mem_univ _⟩⟩

end StatMech.FK.PeriodicPlanar
