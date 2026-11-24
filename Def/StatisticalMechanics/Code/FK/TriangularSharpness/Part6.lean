module
public import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
public import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
public import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable def triangularBoxDenom
    (n : Nat) (q beta : Real) : Real :=
  let M := (Finset.univ : Finset (TriangularBoxVertex n)).sup'
    ⟨triangularBoxRoot n, Finset.mem_univ _⟩ (fun x => ∑ k : ↑(Finset.Icc 1 n),
      triangularBoxConnMass n q beta x k)
  2 * (1 + M) / (n : Real)

end StatMech.FK.PeriodicPlanar
