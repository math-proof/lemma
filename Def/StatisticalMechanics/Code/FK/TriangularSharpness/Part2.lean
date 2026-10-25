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
import Instance.StatisticalMechanics.Code.FK.TriangularSharpness
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

def triangularBoxRoot (n : Nat) : TriangularBoxVertex n := ⟨0, by simp⟩

noncomputable def triangularBoxShell (n k : Nat) : Finset (TriangularBoxVertex n) :=
  Finset.univ.filter fun x => (x.1 : Site 2) ∈ vertexBoundary 2 k

noncomputable def triangularBoxEndU (n : Nat) :
    (triangularBoxGraph n).edgeSet → TriangularBoxVertex n :=
  fun e => e.1.out.1

noncomputable def triangularBoxEndV (n : Nat) :
    (triangularBoxGraph n).edgeSet → TriangularBoxVertex n :=
  fun e => e.1.out.2

end StatMech.FK.PeriodicPlanar
