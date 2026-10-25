/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable def triangularBoxBoundaryGraph (n : Nat) :
    SimpleGraph (TriangularBoxVertex n) :=
  boundaryCliqueGraph fun x => x ∈ triangularBoxShell n n

noncomputable def triangularBoxCrossMass
    (n : Nat) (q beta : Real) : Real :=
  FK.activeBCProbOf (triangularBoxGraph n) (triangularBoxBoundaryGraph n)
    (FK.betaParams (fun _ => 1) beta) q
    (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
      (triangularBoxRoot n) (triangularBoxShell n n))

noncomputable def triangularBoxConnMass
    (n : Nat) (q beta : Real) (x : TriangularBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (triangularBoxGraph n) (triangularBoxBoundaryGraph n)
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (triangularBoxEndU n)
      (triangularBoxEndV n) omega x (triangularBoxShell n k) then 1 else 0)


noncomputable def triangularInnerCrossInd (n : Nat) :
    ConfigSpace (triangularBoxGraph (2 * n)).edgeSet → Real := fun omega =>
  (openCrossEvent (triangularBoxEndU n) (triangularBoxEndV n)
    (triangularBoxRoot n) (triangularBoxShell n n)).indicator (fun _ => 1)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)

end StatMech.FK.PeriodicPlanar
