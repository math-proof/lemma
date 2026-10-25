/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part5
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

open StatMech.OSSS.ReachBoxCrossing

open StatMech.OSSS.RevealmentTranslation

noncomputable def hexagonalBoxCenteredShell
    (n : Nat) (x : HexagonalBoxVertex n) (k : Nat) :
    Finset (HexagonalBoxVertex n) :=
  Finset.univ.filter fun y => centeredRadius x.1.1 y.1.1 = k

noncomputable def hexagonalOuterCenteredConn
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (hexagonalBoxCenteredShell n x k) then (1 : Real) else 0)


end StatMech.FK.PeriodicPlanar
