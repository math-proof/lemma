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
import Def.StatisticalMechanics.Code.FK.TriangularSharpness.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

@[simp] theorem triangularBox_end_coherent
    (n : Nat) (e : (triangularBoxGraph n).edgeSet) :
    e.1 = s(triangularBoxEndU n e, triangularBoxEndV n e) := by
  exact e.1.out_eq.symm

theorem triangularBox_end_adj
    (n : Nat) (e : (triangularBoxGraph n).edgeSet) :
    (triangularBoxGraph n).Adj
      (triangularBoxEndU n e) (triangularBoxEndV n e) := by
  have he : (triangularBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    have hout : s(e.1.out.1, e.1.out.2) = e.1 := e.1.out_eq
    rw [hout]
    exact e.2
  exact he


end StatMech.FK.PeriodicPlanar
