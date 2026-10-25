/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWWindingSideObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparationObstruction.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWCanonicalOrbitSides
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

noncomputable def rlc_windingSideCounterexampleGap :
    RlcAxisBarrierGap rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft where
  lower := -1
  upper := 1
  lower_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  upper_mem := by
    rw [rlc_mem_axisHeights_iff,
      rlc_traceSplitCounterexample_left_vertices]
    simp
  start_le := by
    have hstart : (rlc_traceSplitCounterexampleRight.1.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleRight.1 := by
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).start_mem_support
    rw [rlc_traceSplitCounterexample_right_vertices] at hstart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hstart
    rcases hstart with h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · have hx := rlc_traceSplitCounterexampleRight.1.1.2.2
      rw [h] at hx
      simp at hx
  lower_lt_upper := by omega
  upper_le_finish := by
    have hend : (rlc_traceSplitCounterexampleLeft.1.2.1 : Site 2) ∈
        rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 := by
      exact (rlc_mem_ambientCrossingWalk_support_iff_pathVertices _ _).1
        (rlc_ambientCrossingWalk _).end_mem_support
    rw [rlc_traceSplitCounterexample_left_vertices] at hend
    simp only [Finset.mem_insert, Finset.mem_singleton] at hend
    rcases hend with h | h | h | h
    · have hx := rlc_traceSplitCounterexampleLeft.1.2.1.2.2
      rw [h] at hx
      simp at hx
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
  interior_free := by
    intro t hlow hupp
    have ht : t = 0 := by omega
    subst t
    rw [rlc_axis_mem_connectorBarrier_iff]
    rw [rlc_traceSplitCounterexample_right_vertices,
      rlc_traceSplitCounterexample_left_vertices]
    simp

def rlc_windingSideCounterexampleConfig : ConfigSpace (Sym2 (Site 2)) :=
  fun _ => false

end Universality
end StatMech
