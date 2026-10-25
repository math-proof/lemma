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
import Def.StatisticalMechanics.Code.FK.HexagonalSharpness.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

theorem hexagonalInnerCrossInd_monotone (n : Nat) :
    Monotone (hexagonalInnerCrossInd n) := by
  intro omega eta hle
  apply (openCrossEvent_isIncreasing (hexagonalBoxEndU n)
    (hexagonalBoxEndV n) (hexagonalBoxRoot n)
    (hexagonalBoxShell n n)).indicator_monotone
  intro e
  exact hle (hexagonalBoxEdgeLE (by omega : n ≤ 2 * n) e)

theorem hexagonalInnerCrossInd_idem (n : Nat)
    (omega : ConfigSpace (hexagonalBoxGraph (2 * n)).edgeSet) :
    hexagonalInnerCrossInd n omega * hexagonalInnerCrossInd n omega =
      hexagonalInnerCrossInd n omega := by
  unfold hexagonalInnerCrossInd
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

end StatMech.FK.PeriodicPlanar
