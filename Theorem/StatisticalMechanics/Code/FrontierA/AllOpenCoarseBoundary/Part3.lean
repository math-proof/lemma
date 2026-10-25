/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Def.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


@[simp] theorem mem_faithfulAllOpenTrifIndicesInBox
    {omega : ConfigSpace (Sym2 (Site 2))} {L N : ℕ} {j : Site 2} :
    j ∈ faithfulAllOpenTrifIndicesInBox omega L N ↔
      j ∈ box 2 N ∧ FaithfulAllOpenTrifAt omega L j := by
  classical
  simp [faithfulAllOpenTrifIndicesInBox]


theorem faithfulAllOpenTrifIndicesInBox_count
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    (faithfulAllOpenTrifIndicesInBox omega L N).card ≤
      (vertexBoundary_finite 2
        ((2 * L + 1) * N + L + 1)).toFinset.card := by
  apply faithfulAllOpenTrifAt_count_inner omega L ((2 * L + 1) * N)
  · intro j hj
    exact (mem_faithfulAllOpenTrifIndicesInBox.mp hj).2
  · intro j hj
    exact bgf2_centre_mem_scaled_box
      (mem_faithfulAllOpenTrifIndicesInBox.mp hj).1


theorem allOpenTrif_boundary_witnesses
    {omega : ConfigSpace (Sym2 (Site 2))} {L R : ℕ} (hR : 1 ≤ R)
    (h : bao_AllOpenTrif omega L)
    (harms : ∀ a : Site 2, bc67_GnIncident omega L 0 a →
      (cluster 2 (removeSites (bc61_boxAround 2 L 0) omega) a).Infinite →
      a ∈ box 2 R) :
    ∃ z1 z2 z3 : Site 2,
      z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧
      z3 ∈ vertexBoundary 2 R ∧
      bgf2_q omega L z1 ≠ 0 ∧ bgf2_q omega L z2 ≠ 0 ∧
      bgf2_q omega L z3 ≠ 0 ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z1) ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z2) ∧
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
          (bgf2_q omega L z2) (bgf2_q omega L z3) := by
  obtain ⟨htri, hopen⟩ := h
  have h0 : bgf2_IndexAllOpen omega L 0 :=
    bgf2_indexAllOpen_zero_of_bff hopen
  obtain ⟨a1, a2, a3, ⟨hi1, hi2, hi3⟩, ⟨hinf1, hinf2, hinf3⟩,
    hcut12, hcut13, hcut23⟩ := htri
  obtain ⟨z1, hz1, hr1⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a1
      (harms a1 hi1 hinf1) hinf1
  obtain ⟨z2, hz2, hr2⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a2
      (harms a2 hi2 hinf2) hinf2
  obtain ⟨z3, hz3, hr3⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR 0 a3
      (harms a3 hi3 hinf3) hinf3
  have ha1out : a1 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf1
  have ha2out : a2 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf2
  have ha3out : a3 ∉ bc61_boxAround 2 L 0 := stac_infiniteCluster_notMem _ _ hinf3
  have hz1out : z1 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr1.symm
    exact ha1out (heq ▸ hz)
  have hz2out : z2 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr2.symm
    exact ha2out (heq ▸ hz)
  have hz3out : z3 ∉ bc61_boxAround 2 L 0 := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L 0) omega hz hr3.symm
    exact ha3out (heq ▸ hz)
  have hnz1 : bgf2_q omega L z1 ≠ 0 := by
    intro hz
    exact hz1out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hnz2 : bgf2_q omega L z2 ≠ 0 := by
    intro hz
    exact hz2out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hnz3 : bgf2_q omega L z3 ≠ 0 := by
    intro hz
    exact hz3out ((bgf2_q_eq_zero_iff_mem h0).1 hz)
  have hreach (a z : Site 2) (hi : bc67_GnIncident omega L 0 a)
      (hr : Connected 2 (removeSites (bc61_boxAround 2 L 0) omega) a z) :
      (bgf2_Gf omega L).Reachable 0 (bgf2_q omega L z) := by
    obtain ⟨b, hb, hba⟩ := hi
    have hqb : bgf2_q omega L b = 0 :=
      (bgf2_q_eq_zero_iff_mem h0).2 hb
    have hc : Connected 2 omega b z := hba.reachable.trans (bc61_connected_of_cut hr)
    simpa [hqb] using bgf2_reach_of_connected (L := L) hc
  refine ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
    hreach a1 z1 hi1 hr1, hreach a2 z2 hi2 hr2,
    hreach a3 z3 hi3 hr3, ?_, ?_, ?_⟩
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z1 z2 rfl rfl hnz1 hnz2
    exact hcut12 (hr1.trans (hc'.trans hr2.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z1 z3 rfl rfl hnz1 hnz3
    exact hcut13 (hr1.trans (hc'.trans hr3.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_aux h0 hc z2 z3 rfl rfl hnz2 hnz3
    exact hcut23 (hr2.trans (hc'.trans hr3.symm))

end StatMech.FrontierA
