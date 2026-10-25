/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable def hexagonalBoxBoundaryGraph (n : Nat) :
    SimpleGraph (HexagonalBoxVertex n) :=
  boundaryCliqueGraph fun x => x ∈ hexagonalBoxShell n n

noncomputable def hexagonalBoxCrossMass
    (n : Nat) (q beta : Real) : Real :=
  FK.activeBCProbOf (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
    (FK.betaParams (fun _ => 1) beta) q
    (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (hexagonalBoxRoot n) (hexagonalBoxShell n n))

noncomputable def hexagonalBoxConnMass
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph n) (hexagonalBoxBoundaryGraph n)
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n)
      (hexagonalBoxEndV n) omega x (hexagonalBoxShell n k) then 1 else 0)


noncomputable def hexagonalInnerCrossInd (n : Nat) :
    ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet → Real := fun omega =>
  (openCrossEvent (hexagonalBoxEndU n) (hexagonalBoxEndV n)
    (hexagonalBoxRoot n) (hexagonalBoxShell n n)).indicator (fun _ => 1)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)

end StatMech.FK.PeriodicPlanar
