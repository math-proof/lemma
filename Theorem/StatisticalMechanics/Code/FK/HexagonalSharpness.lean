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
import Def.StatisticalMechanics.Code.FK.HexagonalSharpness.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

@[simp] theorem hexagonalBox_end_coherent
    (n : Nat) (e : (hexagonalBoxGraph n).edgeSet) :
    e.1 = s(hexagonalBoxEndU n e, hexagonalBoxEndV n e) := by
  exact e.1.out_eq.symm

theorem hexagonalBox_end_adj
    (n : Nat) (e : (hexagonalBoxGraph n).edgeSet) :
    (hexagonalBoxGraph n).Adj
      (hexagonalBoxEndU n e) (hexagonalBoxEndV n e) := by
  have he : (hexagonalBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


end StatMech.FK.PeriodicPlanar
