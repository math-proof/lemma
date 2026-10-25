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
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

def triangularBoxEdgeLE {n m : Nat} (h : n ≤ m) :
    (triangularBoxGraph n).edgeSet → (triangularBoxGraph m).edgeSet := fun e =>
  ⟨innerEdgeLE 2 h e.1, by
    have hpair : innerEdgeLE 2 h e.1 =
        s(boxVertInclLE 2 h e.1.out.1, boxVertInclLE 2 h e.1.out.2) := by
      unfold innerEdgeLE
      calc
        Sym2.map (boxVertInclLE 2 h) e.1 =
            Sym2.map (boxVertInclLE 2 h) s(e.1.out.1, e.1.out.2) := by
          exact congrArg (Sym2.map (boxVertInclLE 2 h)) e.1.out_eq.symm
        _ = _ := by rw [Sym2.map_mk]
    rw [hpair, SimpleGraph.mem_edgeSet]
    have he : (triangularBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
      rw [← SimpleGraph.mem_edgeSet,
        show s(e.1.out.1, e.1.out.2) = e.1 from e.1.out_eq]
      exact e.2
    exact he⟩

end StatMech.FK.PeriodicPlanar
