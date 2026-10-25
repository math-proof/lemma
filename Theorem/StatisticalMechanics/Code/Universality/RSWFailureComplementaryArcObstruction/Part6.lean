/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part6
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_rightVertex_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_connectorBarrier, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl hz))

theorem rlc_stdf_leftVertex_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_connectorBarrier, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr hz))

theorem rlc_stdf_gapRegionBlockedNeighbors_mem_barrier {z : Site 2}
    (hz : z ∈ rlc_stdf_gapRegionBlockedNeighbors) :
    z ∈ rlc_connectorBarrier rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft := by
  simp only [rlc_stdf_gapRegionBlockedNeighbors, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · apply rlc_stdf_rightVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp
  · apply rlc_stdf_rightVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_right_vertices]
    simp
  · apply rlc_stdf_leftVertex_mem_barrier
    rw [rlc_scaleTwoDoubleFailure_left_vertices]
    simp

theorem rlc_stdf_gapRegionCore_step {u v : Site 2}
    (hu : u ∈ rlc_stdf_gapRegionCore)
    (huv : (hypercubicLattice 2).Adj u v)
    (hvAllowed : v ∈ rlc_connectorAllowed
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft) :
    v ∈ rlc_stdf_gapRegionCore := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  simp only [rlc_stdf_gapRegionCore, Finset.mem_insert,
    Finset.mem_singleton] at hu
  have hvCases : v ∈ rlc_stdf_gapRegionCore ∨
      v ∈ rlc_stdf_gapRegionBlockedNeighbors ∨
        v = (![-1, -3] : Site 2) := by
    rcases hu with rfl | rfl | rfl
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
    · rw [candFinset_face] at hvCand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
      rcases hvCand with rfl | rfl | rfl | rfl <;>
        simp [rlc_stdf_gapRegionCore, rlc_stdf_gapRegionBlockedNeighbors]
  rcases hvCases with hvCore | hvBlocked | hvOutside
  · exact hvCore
  · exact False.elim ((Finset.mem_sdiff.mp hvAllowed).2
      (rlc_stdf_gapRegionBlockedNeighbors_mem_barrier hvBlocked))
  · subst v
    have hvBox := (Finset.mem_sdiff.mp hvAllowed).1
    simp [rlc_connectorBox, mem_rect] at hvBox

theorem rlc_stdf_axisGapRegion_subset_core {z : Site 2}
    (hz : z ∈ rlc_axisGapRegion rlc_scaleTwoDoubleFailureGap) :
    z ∈ rlc_stdf_gapRegionCore := by
  have hzSet : z ∈ rlc_axisGapRegionSet rlc_scaleTwoDoubleFailureGap := by
    simpa [rlc_axisGapRegion] using hz
  obtain ⟨hzAllowed, hseedAllowed, hreach⟩ := hzSet
  obtain ⟨p⟩ := hreach
  have walk_stays {x y :
      (rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
        rlc_scaleTwoDoubleFailureLeft : Set (Site 2))}
      (w : ((hypercubicLattice 2).induce
        (rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
          rlc_scaleTwoDoubleFailureLeft : Set (Site 2))).Walk x y)
      (hx : (x : Site 2) ∈ rlc_stdf_gapRegionCore) :
      (y : Site 2) ∈ rlc_stdf_gapRegionCore := by
    induction w with
    | nil => exact hx
    | @cons a b c hab w ih =>
        exact ih (rlc_stdf_gapRegionCore_step hx hab b.2)
  have hseed :
      (rlc_scaleTwoDoubleFailureGap.seedVertex : Site 2) ∈
        rlc_stdf_gapRegionCore := by
    simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.seedVertex,
      rlc_stdf_gapRegionCore]
  exact walk_stays p hseed

theorem rlc_stdf_axisGapEdge_location {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap) :
    e = rlc_scaleTwoDoubleFailureGap.firstEdge ∨
      ∃ z ∈ rlc_stdf_gapRegionCore, z ∈ e := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with hinterior | hfirst
  · right
    obtain ⟨_edges, z, hzRegion, hzEdge⟩ := Finset.mem_filter.mp hinterior
    exact ⟨z, rlc_stdf_axisGapRegion_subset_core hzRegion, hzEdge⟩
  · left
    simpa using hfirst

end Universality
end StatMech
