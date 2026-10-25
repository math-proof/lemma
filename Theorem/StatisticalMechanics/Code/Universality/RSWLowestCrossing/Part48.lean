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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part47
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_jointBottomTraceBoundary_subset_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomTraceBoundary gamma delta ⊆
      (rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1 := by
  rintro v ⟨_vR, hvPath, _u, _hu, _hadj⟩
  exact hvPath


theorem rlc_jointBottomTraceBoundary_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomTraceBoundary gamma delta).Finite :=
  ((rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1).finite_toSet).subset (by
    intro v hv
    simpa using rlc_jointBottomTraceBoundary_subset_paths gamma delta hv)


theorem rlc_jointBottomTraceBoundary_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hv : v ∈ rlc_jointBottomTraceBoundary gamma delta) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  rcases hv with ⟨hvR, hvPath, u, hu, hadj⟩
  exact rlc_jointBottomSet_boundary_trace_safe
    hn gamma delta hu hvR hadj hvPath


theorem rlc_bottomTraceVertex_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hvBottom : v ∈ bottomSide 0 (2 * n) (-n) n)
    (_hvPath : v ∈ rlc_pathVertices gamma.1 ∨
      v ∈ rlc_pathVertices delta.1) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  intro hvTop
  rcases hvTop with hvTopGamma | hvTopDelta
  · by_cases hvGamma : v ∈ rlc_pathVertices gamma.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path gamma)) hvTopGamma hvGamma
    · have hvBelowGamma : v ∈ rlc_strictBelowSet gamma :=
        ⟨v, hvBottom, hvGamma, SimpleGraph.Reachable.refl v⟩
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn gamma))
          hvTopGamma hvBelowGamma
  · by_cases hvDelta : v ∈ rlc_pathVertices delta.1
    · exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_path delta)) hvTopDelta hvDelta
    · have hvBelowDelta : v ∈ rlc_strictBelowSet delta :=
        ⟨v, hvBottom, hvDelta, SimpleGraph.Reachable.refl v⟩
      exact (Set.disjoint_left.mp
        (rlc_strictTopSet_disjoint_strictBelowSet hn delta))
          hvTopDelta hvBelowDelta


end Universality
end StatMech
