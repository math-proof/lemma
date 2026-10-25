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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part6
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_betweenEvent_isIncreasing {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) : IsIncreasing (rlc_betweenEvent P Q) := by
  intro omega omega' homega
  rintro ⟨x, y, hxy⟩
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono homega hxy⟩


theorem rlc_betweenEvent_dependsOn {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) :
    DependsOn ((rlc_betweenEvent P Q).indicator (fun _ => (1 : ℝ)))
      (StatMech.Percolation.edgesWithinFinset (rlc_rectFinset a b c d) :
        Set (Sym2 (Site 2))) := by
  intro omega omega' hagree
  have hcoord : ∀ u v : Site 2, u ∈ rect a b c d → v ∈ rect a b c d →
      omega s(u, v) = omega' s(u, v) := by
    intro u v hu hv
    apply hagree
    change s(u, v) ∈ StatMech.Percolation.edgesWithinFinset (rlc_rectFinset a b c d)
    rw [StatMech.Percolation.mem_edgesWithinFinset]
    exact ⟨u, by simpa using hu, v, by simpa using hv, rfl⟩
  have hG : openSubgraphInduce 2 omega (rect a b c d) =
      openSubgraphInduce 2 omega' (rect a b c d) := by
    apply SimpleGraph.ext
    ext u v
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [hcoord u v u.2 v.2]
  have hiff : omega ∈ rlc_betweenEvent P Q ↔ omega' ∈ rlc_betweenEvent P Q := by
    simp only [rlc_betweenEvent, Set.mem_setOf_eq, ConnectedWithin, hG]
  by_cases hmem : omega ∈ rlc_betweenEvent P Q
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

theorem rlc_betweenEvent_measurableSet {a b c d : ℤ}
    (P Q : Finset (rect a b c d)) : MeasurableSet (rlc_betweenEvent P Q) :=
  measurableSet_of_dependsOn (rlc_betweenEvent_dependsOn P Q)


end Universality
end StatMech
