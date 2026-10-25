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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part51
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_path_start_mem_vertices {a b c d : ℤ}
    (gamma : RlcCrossingPath a b c d) :
    (gamma.1 : Site 2) ∈ rlc_pathVertices gamma := by
  simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
  exact ⟨⟨(gamma.1 : Site 2), leftSide_subset gamma.1.2⟩,
    gamma.2.2.1.start_mem_support, rfl⟩

theorem rlc_rightPathStrictlyBelow_irrefl {n : ℤ}
    (gamma : RlcRightDiagonalPath n) :
    ¬ rlc_rightPathStrictlyBelow gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictBelowSet_disjoint_path gamma))
    (h hstart) hstart

theorem rlc_leftPathStrictlyAbove_irrefl {n : ℤ}
    (gamma : RlcLeftDiagonalPath n) :
    ¬ rlc_leftPathStrictlyAbove gamma gamma := by
  intro h
  have hstart := rlc_path_start_mem_vertices gamma.1
  exact (Set.disjoint_left.mp (rlc_strictAboveSet_disjoint_path gamma))
    (h hstart) hstart

end Universality
end StatMech
