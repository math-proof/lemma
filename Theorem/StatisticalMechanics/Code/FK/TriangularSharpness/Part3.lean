module
public import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
public import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
public import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
public import Def.StatisticalMechanics.Code.FK.TriangularSharpness.Part4
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

theorem triangularInnerCrossInd_monotone (n : Nat) :
    Monotone (triangularInnerCrossInd n) := by
  intro omega eta hle
  apply (openCrossEvent_isIncreasing (triangularBoxEndU n)
    (triangularBoxEndV n) (triangularBoxRoot n)
    (triangularBoxShell n n)).indicator_monotone
  intro e
  exact hle (triangularBoxEdgeLE (by omega : n ≤ 2 * n) e)

theorem triangularInnerCrossInd_idem (n : Nat)
    (omega : ConfigSpace (triangularBoxGraph (2 * n)).edgeSet) :
    triangularInnerCrossInd n omega * triangularInnerCrossInd n omega =
      triangularInnerCrossInd n omega := by
  unfold triangularInnerCrossInd
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

end StatMech.FK.PeriodicPlanar
