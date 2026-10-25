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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part38
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_rot180_mem_strictBottom_of_mem_strictTop {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {z : Site 2}
    (hz : z ∈ rlc_strictTopSet gamma) :
    rlc_rot180 z ∈ rlc_strictBottomSet (rlc_rot180RightPath gamma) := by
  obtain ⟨x, hxTop, hxPath, hreach⟩ := hz
  obtain ⟨w⟩ := hreach
  have hxBottom : rlc_rot180 x ∈ bottomSide (-2 * n) 0 (-n) n := by
    rw [mem_bottomSide]
    rw [mem_topSide] at hxTop
    refine ⟨(rlc_rot180_mem_rightRect_iff_leftRect n x).mp hxTop.1, ?_⟩
    simp only [rlc_rot180_one, hxTop.2]
  have hxNot : rlc_rot180 x ∉
      rlc_pathVertices (rlc_rot180RightPath gamma).1 := by
    intro hx
    rw [rlc_pathVertices_rot180RightPath, Finset.mem_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := rlc_rot180.injective (by simpa using hyx)
    exact hxPath (this ▸ hy)
  exact ⟨rlc_rot180 x, hxBottom, hxNot,
    ⟨w.map (rlc_rot180RightAvoidHom gamma)⟩⟩

end Universality
end StatMech
