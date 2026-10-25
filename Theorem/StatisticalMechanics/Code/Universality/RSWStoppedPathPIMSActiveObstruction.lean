/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_activeGap_region_cases {z : Site 2}
    (hz : z ∈ rlc_axisGapRegion rlc_windingSideCounterexampleGap) :
    z = ![-1, 0] ∨ z = ![0, 0] ∨ z = ![1, 0] := by
  have hzSet : z ∈ rlc_axisGapRegionSet
      rlc_windingSideCounterexampleGap := by
    simpa [rlc_axisGapRegion] using hz
  obtain ⟨hzAllowed, _hseed, _hreach⟩ := hzSet
  have hzBox := (Finset.mem_sdiff.mp hzAllowed).1
  have hzNotBarrier := (Finset.mem_sdiff.mp hzAllowed).2
  rw [rlc_connectorBox, Set.Finite.mem_toFinset, mem_rect] at hzBox
  rw [rlc_connectorBarrier] at hzNotBarrier
  simp only [Finset.mem_union, not_or] at hzNotBarrier
  rw [rlc_traceSplitCounterexample_right_vertices,
    rlc_traceSplitCounterexample_left_vertices] at hzNotBarrier
  simp [rlc_flipX, rlc_flipXFun] at hzNotBarrier
  have hx : z 0 = -2 ∨ z 0 = -1 ∨ z 0 = 0 ∨ z 0 = 1 ∨ z 0 = 2 := by
    omega
  have hy : z 1 = -1 ∨ z 1 = 0 ∨ z 1 = 1 := by
    omega
  rcases hx with hx | hx | hx | hx | hx <;>
    rcases hy with hy | hy | hy
  all_goals
    have hzEq : z = ![z 0, z 1] := by
      ext i
      fin_cases i <;> simp
    rw [hzEq, hx, hy] at hzNotBarrier ⊢
    try simp at hzNotBarrier ⊢

theorem rlc_activeGap_zero_mem_region :
    (![0, 0] : Site 2) ∈
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
  simpa [rlc_windingSideCounterexampleGap,
    RlcAxisBarrierGap.seedVertex] using
      (rlc_windingSideCounterexampleGap.seedVertex_mem_region_of_lt
        (by norm_num) (by norm_num [rlc_windingSideCounterexampleGap]))

theorem rlc_activeGap_one_mem_region :
    (![1, 0] : Site 2) ∈
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
  let G := rlc_windingSideCounterexampleGap
  let A := rlc_connectorAllowed rlc_traceSplitCounterexampleRight
    rlc_traceSplitCounterexampleLeft
  have hseed : G.seedVertex ∈ A :=
    G.seedVertex_mem_allowed_of_lt (by norm_num)
      (by norm_num [G, rlc_windingSideCounterexampleGap])
  have hone : (![1, 0] : Site 2) ∈ A := by
    rw [show A = rlc_connectorAllowed rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft by rfl]
    rw [rlc_connectorAllowed, Finset.mem_sdiff]
    constructor
    · simp [rlc_connectorBox, mem_rect]
    · rw [rlc_connectorBarrier,
        rlc_traceSplitCounterexample_right_vertices,
        rlc_traceSplitCounterexample_left_vertices]
      simp [rlc_flipX, rlc_flipXFun]
  have hadj :
      ((hypercubicLattice 2).induce (A : Set (Site 2))).Adj
        ⟨G.seedVertex, by simpa using hseed⟩
        ⟨![1, 0], by simpa using hone⟩ := by
    change (hypercubicLattice 2).Adj G.seedVertex (![1, 0] : Site 2)
    simp [G, rlc_windingSideCounterexampleGap,
      RlcAxisBarrierGap.seedVertex, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have honeSet : (![1, 0] : Site 2) ∈ rlc_axisGapRegionSet G :=
    ⟨hone, hseed, hadj.reachable⟩
  simpa [G, rlc_axisGapRegion] using honeSet

theorem rlc_activeGap_sourceA_mem :
    s((![1, -1] : Site 2), ![1, 0]) ∈
      rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![1, -1], by simp [rlc_connectorBox, mem_rect],
        ![1, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![1, 0], rlc_activeGap_one_mem_region,
      Sym2.mem_mk_right _ _⟩⟩

theorem rlc_activeGap_sourceB_mem :
    s((![0, 0] : Site 2), ![1, 0]) ∈
      rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![0, 0], by simp [rlc_connectorBox, mem_rect],
        ![1, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, 0], rlc_activeGap_zero_mem_region,
      Sym2.mem_mk_left _ _⟩⟩

theorem rlc_activeGap_sourceC_mem :
    s((![-1, 0] : Site 2), ![0, 0]) ∈
      rlc_axisGapEdges rlc_windingSideCounterexampleGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![-1, 0], by simp [rlc_connectorBox, mem_rect],
        ![0, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, 0], rlc_activeGap_zero_mem_region,
      Sym2.mem_mk_right _ _⟩⟩


end
end StatMech.Universality
