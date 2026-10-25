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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part48
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_jointBottomTraceFrontier_subset_paths {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    rlc_jointBottomTraceFrontier gamma delta ⊆
      (rlc_pathVertices gamma.1 : Set (Site 2)) ∪
        rlc_pathVertices delta.1 := by
  rintro v (hvBoundary | ⟨_hvBottom, hvPath⟩)
  · exact rlc_jointBottomTraceBoundary_subset_paths gamma delta hvBoundary
  · exact hvPath

theorem rlc_jointBottomTraceFrontier_finite {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    (rlc_jointBottomTraceFrontier gamma delta).Finite :=
  ((rlc_pathVertices gamma.1 ∪ rlc_pathVertices delta.1).finite_toSet).subset (by
    intro v hv
    simpa using rlc_jointBottomTraceFrontier_subset_paths gamma delta hv)


theorem rlc_jointBottomTraceFrontier_safe {n : ℤ} (hn : 0 < n)
    (gamma delta : RlcRightDiagonalPath n) {v : Site 2}
    (hv : v ∈ rlc_jointBottomTraceFrontier gamma delta) :
    v ∉ rlc_rightUpperUnionSet gamma delta := by
  rcases hv with hvBoundary | ⟨hvBottom, hvPath⟩
  · exact rlc_jointBottomTraceBoundary_safe hn gamma delta hvBoundary
  · exact rlc_bottomTraceVertex_safe hn gamma delta hvBottom hvPath


end Universality
end StatMech
