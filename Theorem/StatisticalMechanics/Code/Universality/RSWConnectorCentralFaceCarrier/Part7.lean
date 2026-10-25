/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcBookFaithfulTracePair.right_vertex_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1)
    (hne : z ≠ (gamma.1.1 : Site 2)) :
    0 < z 0 := by
  have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
  rw [mem_rect] at hzRect
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    exact hne (h.right_axis_unique hz hz0)
  omega


theorem RlcBookFaithfulTracePair.left_vertex_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma'.1)
    (hne : z ≠ (gamma'.1.2.1 : Site 2)) :
    z 0 < 0 := by
  have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
  rw [mem_rect] at hzRect
  have hz0 : z 0 ≠ 0 := by
    intro hz0
    exact hne (h.left_axis_unique hz hz0)
  omega


theorem RlcBookFaithfulTracePair.axis_contacts_strict {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (h : RlcBookFaithfulTracePair gamma gamma') :
    (gamma.1.1 : Site 2) 1 < (gamma'.1.2.1 : Site 2) 1 := by
  have hright := h.toRlcBookPositionedTracePair.right_axis_strict
  have hleft := h.toRlcBookPositionedTracePair.left_axis_strict
  omega


theorem rlc_traceSplitCounterexample_bookPositioned :
    RlcBookPositionedTracePair rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft := by
  constructor
  · rw [Finset.disjoint_left]
    intro z hzR hzL
    rw [rlc_traceSplitCounterexample_right_vertices] at hzR
    rw [rlc_traceSplitCounterexample_left_vertices] at hzL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzR hzL
    rcases hzR with rfl | rfl | rfl | rfl <;> simp_all
  · change (-1 : Int) < 0
    norm_num
  · change (-1 : Int) < 0
    norm_num


theorem rlc_scaleTwoDoubleFailure_not_bookPositioned :
    ¬ RlcBookPositionedTracePair rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  intro h
  have hstrict := h.left_axis_strict
  change 0 < (0 : Int) at hstrict
  omega


theorem rlc_scaleTwo_centralFace_mem_region :
    rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft :=
  rlc_connectorCentralFace_mem_region _ _ (by norm_num)

end
end StatMech.Universality
