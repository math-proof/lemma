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
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable def triangularOuterInnerConn
    (n : Nat) (q beta : Real) (x : TriangularBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (triangularBoxGraph (2 * n))
      (triangularBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (triangularBoxEndU n) (triangularBoxEndV n)
      (restrictConfig (triangularBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (triangularBoxShell n k) then 1 else 0)

noncomputable def triangularOuterInnerDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularOuterInnerConn n q beta x k)
  2 * (1 + M) / (n : Real)

noncomputable def triangularOuterInnerTheta
    (q beta : Real) (n : Nat) : Real :=
  if n = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (triangularBoxGraph (2 * n))
        (triangularBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q)
      (triangularInnerCrossInd n)

noncomputable def triangularOuterInnerThetaPrime
    (n : Nat) (q beta : Real) : Real :=
  deriv (fun b => triangularOuterInnerTheta q b n) beta

noncomputable def triangularOuterInnerSig
    (n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, triangularOuterInnerTheta q beta k

end StatMech.FK.PeriodicPlanar
