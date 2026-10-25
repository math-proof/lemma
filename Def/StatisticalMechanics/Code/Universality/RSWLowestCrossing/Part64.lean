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
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part64
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


noncomputable def rlc_rightLeftTraceMinSide {n : ℤ}
    (gamma delta : RlcRightDiagonalPath n) :
    leftSide 0 (2 * n) (-n) n := by
  let z := rlc_rightLeftTraceMinVertex gamma delta
  have hzUnion := rlc_rightLeftTraceMinVertex_mem_union gamma delta
  have hzRect : z ∈ rect 0 (2 * n) (-n) n := by
    rcases Finset.mem_union.mp hzUnion with hz | hz
    · exact rlc_pathVertex_mem_rect gamma.1 hz
    · exact rlc_pathVertex_mem_rect delta.1 hz
  exact ⟨z, hzRect, by simp [z, rlc_rightLeftTraceMinVertex]⟩

end Universality
end StatMech
