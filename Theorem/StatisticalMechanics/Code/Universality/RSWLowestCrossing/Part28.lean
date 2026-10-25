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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part27
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_bottomSide_subset_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    bottomSide 0 (2 * n) (-n) n ⊆ rlc_belowSet hn gamma := by
  intro z hz
  apply (rlc_swappedBelowSet_spec hn gamma).1 (crf_swap z)
  · exact (crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hz.1
  · simpa using hz.2

theorem rlc_topSide_disjoint_belowSet {n : ℤ} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) :
    Disjoint (topSide 0 (2 * n) (-n) n) (rlc_belowSet hn gamma) := by
  rw [Set.disjoint_left]
  intro z hzTop hzBelow
  exact (rlc_swappedBelowSet_spec hn gamma).2.1 (crf_swap z)
    ((crf_mem_rect_swap 0 (2 * n) (-n) n z).mp hzTop.1)
    (by simpa using hzTop.2) hzBelow


end Universality
end StatMech
