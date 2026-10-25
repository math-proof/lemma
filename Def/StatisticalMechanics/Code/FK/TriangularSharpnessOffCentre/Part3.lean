/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

noncomputable def triangularInnerKappa (n : Nat) (beta0 : Real) : Real :=
  (reindexedOpenIncidentEdges
    (triangularBoxEdgeLE (by omega : n ≤ 2 * n))
    (triangularBoxEndU n) (triangularBoxEndV n) (triangularBoxRoot n)).prod
      (fun _ => Real.exp (-beta0))

def triangularBoxNeighbor (n : Nat) (hn : 1 ≤ n) (ib : Fin 3 × Bool) :
    TriangularBoxVertex n :=
  ⟨triangularNeighbor 0 ib, by
    rcases ib with ⟨i, b⟩
    fin_cases i <;> cases b <;> intro j <;> fin_cases j <;>
      simp [triangularNeighbor, triangularStep] <;> omega⟩

end StatMech.FK.PeriodicPlanar
