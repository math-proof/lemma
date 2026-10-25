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
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable def hexagonalOuterInnerConn
    (n : Nat) (q beta : Real) (x : HexagonalBoxVertex n) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (hexagonalBoxGraph (2 * n))
      (hexagonalBoxBoundaryGraph (2 * n))
      (FK.betaParams (fun _ => 1) beta) q)
    (fun omega => if ConnOpenSet (hexagonalBoxEndU n) (hexagonalBoxEndV n)
      (restrictConfig (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n)) omega)
      x (hexagonalBoxShell n k) then 1 else 0)

noncomputable def hexagonalOuterInnerDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (HexagonalBoxVertex n)).sup'
    ⟨hexagonalBoxRoot n, Finset.mem_univ _⟩
    (fun x => ∑ k : ↑(Finset.Icc 1 n),
      hexagonalOuterInnerConn n q beta x k)
  2 * (1 + M) / (n : Real)

noncomputable def hexagonalOuterInnerTheta
    (q beta : Real) (n : Nat) : Real :=
  if n = 0 then 1 else
    Lindeberg.mean
      (FK.activeBCProb (hexagonalBoxGraph (2 * n))
        (hexagonalBoxBoundaryGraph (2 * n))
        (FK.betaParams (fun _ => 1) beta) q)
      (hexagonalInnerCrossInd n)

noncomputable def hexagonalOuterInnerThetaPrime
    (n : Nat) (q beta : Real) : Real :=
  deriv (fun b => hexagonalOuterInnerTheta q b n) beta

noncomputable def hexagonalOuterInnerSig
    (n : Nat) (q beta : Real) : Real :=
  ∑ k ∈ Finset.range n, hexagonalOuterInnerTheta q beta k

end StatMech.FK.PeriodicPlanar
