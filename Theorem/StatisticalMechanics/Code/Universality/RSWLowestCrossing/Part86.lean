/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part84
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_axisGapConnectorEvent_dependsOn {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    DependsOn ((rlc_axisGapConnectorEvent G).indicator (fun _ => (1 : ℝ)))
      (rlc_axisGapEdges G : Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hmask : rlc_maskConfig (rlc_axisGapEdges G) omega =
      rlc_maskConfig (rlc_axisGapEdges G) omega' :=
    rlc_maskConfig_congr hagree
  have hevent : omega ∈ rlc_axisGapConnectorEvent G ↔
      omega' ∈ rlc_axisGapConnectorEvent G := by
    simp only [rlc_axisGapConnectorEvent, Set.mem_setOf_eq, hmask]
  by_cases hmem : omega ∈ rlc_axisGapConnectorEvent G
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hevent.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hevent.mpr h))]

theorem rlc_axisGapConnectorEvent_measurableSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    MeasurableSet (rlc_axisGapConnectorEvent G) :=
  measurableSet_of_dependsOn (rlc_axisGapConnectorEvent_dependsOn G)


end Universality
end StatMech
