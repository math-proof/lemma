/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part5
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_right_subset_originalRegion {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
    z ∈ rlc_stdf_originalRegion := by
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_stdf_originalRegion]

theorem rlc_stdf_originalRegion_disjoint_left {z : Site 2}
    (hz : z ∈ rlc_stdf_originalRegion)
    (hzLeft : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    False := by
  rw [rlc_scaleTwoDoubleFailure_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft
  rcases hzLeft with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_stdf_originalRegion] at hz

theorem rlc_stdf_original_open_step {u v : Site 2}
    (hu : u ∈ rlc_stdf_originalRegion)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (hopen : rlc_wiredConnectorConfig
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
      (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
      rlc_scaleTwoDoubleFailureConfig s(u, v) = true) :
    v ∈ rlc_stdf_originalRegion := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hp : e ∈
      rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 ∪
        rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1
  · rw [Finset.mem_union] at hp
    rcases hp with hright | hleft
    · exact rlc_stdf_right_subset_originalRegion
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureRight.1 hright).2
    · exact False.elim (rlc_stdf_originalRegion_disjoint_left hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureLeft.1 hleft).1)
  · have homega : rlc_scaleTwoDoubleFailureConfig e = true := by
      rw [rlc_wiredConnectorConfig, if_neg hp, rlc_maskConfig] at hopen
      split at hopen
      · exact hopen
      · simp at hopen
    have heOpen : e ∈ rlc_scaleTwoDoubleFailureOpenEdges :=
      (rlc_scaleTwoDoubleFailureConfig_eq_true_iff e).mp homega
    simp only [rlc_scaleTwoDoubleFailureOpenEdges, Finset.mem_insert,
      Finset.mem_singleton] at heOpen
    rcases heOpen with he | he | he | he | he <;>
      rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨huv, hvu⟩ | ⟨huv, hvu⟩ <;>
      subst u <;> subst v <;>
      simp [rlc_stdf_originalRegion, mem_rect] at hu hvBox ⊢


theorem rlc_scaleTwoDoubleFailure_original_failure :
    rlc_scaleTwoDoubleFailureConfig ∉
      rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hconn
  let B := rect (-4) 4 (-2) 2
  let eta := rlc_wiredConnectorConfig
    rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
    (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
    rlc_scaleTwoDoubleFailureConfig
  have walk_stays {x y : B}
      (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈ rlc_stdf_originalRegion) :
      (y : Site 2) ∈ rlc_stdf_originalRegion := by
    induction p with
    | nil => exact hx
    | @cons a b c hab p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_stdf_original_open_step hx b.2 hab.2)
  obtain ⟨p⟩ := hconn
  have hlower :
      (rlc_scaleTwoDoubleFailureGap.lowerVertex : Site 2) ∈
        rlc_stdf_originalRegion := by
    simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.lowerVertex,
      rlc_stdf_originalRegion]
  have hupper := walk_stays p hlower
  simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.upperVertex,
    rlc_stdf_originalRegion] at hupper

end Universality
end StatMech
