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
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

def hexagonalBoxVertInclLE {n m : Nat} (h : n ≤ m) :
    HexagonalBoxVertex n → HexagonalBoxVertex m :=
  fun x => ⟨x.1, ⟨box_mono 2 h x.2.1, Set.mem_univ _⟩⟩

def hexagonalBoxEdgeLE {n m : Nat} (h : n ≤ m) :
    (hexagonalBoxGraph n).edgeSet → (hexagonalBoxGraph m).edgeSet := fun e =>
  ⟨Sym2.map (hexagonalBoxVertInclLE h) e.1, by
    have hpair : Sym2.map (hexagonalBoxVertInclLE h) e.1 =
        s(hexagonalBoxVertInclLE h e.1.out.1,
          hexagonalBoxVertInclLE h e.1.out.2) := by
      calc
        Sym2.map (hexagonalBoxVertInclLE h) e.1 =
            Sym2.map (hexagonalBoxVertInclLE h)
              s(e.1.out.1, e.1.out.2) := by
          exact congrArg (Sym2.map (hexagonalBoxVertInclLE h))
            e.1.out_eq.symm
        _ = _ := by rw [Sym2.map_mk]
    rw [hpair, SimpleGraph.mem_edgeSet]
    have he : (hexagonalBoxGraph n).Adj e.1.out.1 e.1.out.2 := by
      rw [← SimpleGraph.mem_edgeSet,
        show s(e.1.out.1, e.1.out.2) = e.1 from e.1.out_eq]
      exact e.2
    simpa [hexagonalBoxGraph, hexagonalBoxEmbedding,
      hexagonalBoxVertInclLE, boxVertInclLE] using he⟩

end StatMech.FK.PeriodicPlanar
