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
import Def.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


theorem faithfulAllOpenTrifAt_boundary_witnesses
    {omega : ConfigSpace (Sym2 (Site 2))} {L R : ℕ} {j : Site 2}
    (hR : 1 ≤ R) (h : FaithfulAllOpenTrifAt omega L j)
    (harms : ∀ a : Site 2,
      bc67_GnIncident omega L (bgf2_centre L j) a →
      (cluster 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite →
      a ∈ box 2 R) :
    ∃ z1 z2 z3 : Site 2,
      z1 ∈ vertexBoundary 2 R ∧ z2 ∈ vertexBoundary 2 R ∧
      z3 ∈ vertexBoundary 2 R ∧
      bgf2_q omega L z1 ≠ bgf2_centre L j ∧
      bgf2_q omega L z2 ≠ bgf2_centre L j ∧
      bgf2_q omega L z3 ≠ bgf2_centre L j ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z1) ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z2) ∧
      (bgf2_Gf omega L).Reachable (bgf2_centre L j) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z2) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z1) (bgf2_q omega L z3) ∧
      ¬ (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable
          (bgf2_q omega L z2) (bgf2_q omega L z3) := by
  obtain ⟨htri, hj⟩ := h
  obtain ⟨a1, a2, a3, ⟨hi1, hi2, hi3⟩, ⟨hinf1, hinf2, hinf3⟩,
    hcut12, hcut13, hcut23⟩ := htri
  obtain ⟨z1, hz1, hr1⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a1
      (harms a1 hi1 hinf1) hinf1
  obtain ⟨z2, hz2, hr2⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a2
      (harms a2 hi2 hinf2) hinf2
  obtain ⟨z3, hz3, hr3⟩ :=
    bc63_coarseArm_reaches_boundary omega L R hR (bgf2_centre L j) a3
      (harms a3 hi3 hinf3) hinf3
  have ha1out := stac_infiniteCluster_notMem _ _ hinf1
  have ha2out := stac_infiniteCluster_notMem _ _ hinf2
  have ha3out := stac_infiniteCluster_notMem _ _ hinf3
  have hzout (a z : Site 2)
      (ha : a ∉ bc61_boxAround 2 L (bgf2_centre L j))
      (hr : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a z) :
      z ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hz
    have heq := stac_removeSites_connected_eq
      (bc61_boxAround 2 L (bgf2_centre L j)) omega hz hr.symm
    exact ha (heq ▸ hz)
  have hz1out := hzout a1 z1 ha1out hr1
  have hz2out := hzout a2 z2 ha2out hr2
  have hz3out := hzout a3 z3 ha3out hr3
  have hnz (z : Site 2)
      (hz : z ∉ bc61_boxAround 2 L (bgf2_centre L j)) :
      bgf2_q omega L z ≠ bgf2_centre L j := by
    intro heq
    exact hz (bgf2_mem_box_centre_iff.mpr
      ((bgf2_q_eq_centre_iff hj).mp heq))
  have hnz1 := hnz z1 hz1out
  have hnz2 := hnz z2 hz2out
  have hnz3 := hnz z3 hz3out
  have hreach (a z : Site 2)
      (hi : bc67_GnIncident omega L (bgf2_centre L j) a)
      (hr : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a z) :
      (bgf2_Gf omega L).Reachable
        (bgf2_centre L j) (bgf2_q omega L z) := by
    obtain ⟨b, hb, hba⟩ := hi
    have hqb : bgf2_q omega L b = bgf2_centre L j :=
      (bgf2_q_eq_centre_iff hj).2 (bgf2_mem_box_centre_iff.mp hb)
    have hc : Connected 2 omega b z :=
      hba.reachable.trans (bc61_connected_of_cut hr)
    simpa [hqb] using bgf2_reach_of_connected (L := L) hc
  refine ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
    hreach a1 z1 hi1 hr1, hreach a2 z2 hi2 hr2,
    hreach a3 z3 hi3 hr3, ?_, ?_, ?_⟩
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z1 z2 rfl rfl hnz1 hnz2
    exact hcut12 (hr1.trans (hc'.trans hr2.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z1 z3 rfl rfl hnz1 hnz3
    exact hcut13 (hr1.trans (hc'.trans hr3.symm))
  · intro hc
    have hc' := bgf2_cut_connected_of_reach_at hj hc z2 z3 rfl rfl hnz2 hnz3
    exact hcut23 (hr2.trans (hc'.trans hr3.symm))


theorem faithfulAllOpenTrifAt_count_le_boundary
    (omega : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (hR : 1 ≤ R)
    (J : Finset (Site 2))
    (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
    (harms : ∀ j ∈ J, ∀ a : Site 2,
      bc67_GnIncident omega L (bgf2_centre L j) a →
      (cluster 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a).Infinite →
      a ∈ box 2 R) :
    J.card ≤ (vertexBoundary_finite 2 R).toFinset.card := by
  classical
  let hubs : Finset (Site 2) := J.image (bgf2_centre L)
  let boundary : Finset (Site 2) :=
    (vertexBoundary_finite 2 R).toFinset.image (bgf2_q omega L)
  have hhubCard : hubs.card = J.card := by
    change (J.image (bgf2_centre L)).card = J.card
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact bgf2_centre_inj hab
  have hboundaryCard : boundary.card ≤
      (vertexBoundary_finite 2 R).toFinset.card := by
    exact Finset.card_image_le
  have hcount : hubs.card ≤ boundary.card := by
    apply finite_cutHub_count_of_ambient (bgf2_Gf omega L) hubs boundary
    intro u hu
    change u ∈ J.image (bgf2_centre L) at hu
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨z1, z2, z3, hz1, hz2, hz3, hnz1, hnz2, hnz3,
      hr1, hr2, hr3, hc12, hc13, hc23⟩ :=
      faithfulAllOpenTrifAt_boundary_witnesses hR (htrif j hjJ)
        (harms j hjJ)
    have ht1 : bgf2_q omega L z1 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z1, by simpa using hz1, rfl⟩
    have ht2 : bgf2_q omega L z2 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z2, by simpa using hz2, rfl⟩
    have ht3 : bgf2_q omega L z3 ∈ boundary := by
      apply Finset.mem_image.mpr
      exact ⟨z3, by simpa using hz3, rfl⟩
    have hdel : (bgf2_Gf omega L).deleteIncidenceSet (bgf2_centre L j) =
        bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j) := by
      ext a b
      rw [SimpleGraph.deleteIncidenceSet_adj, bkg_deleteVertex_adj]
    refine ⟨bgf2_q omega L z1, bgf2_q omega L z2,
      bgf2_q omega L z3, ht1, ht2, ht3, hnz1.symm, hnz2.symm,
      hnz3.symm, hr1, hr2, hr3, ?_, ?_, ?_⟩
    · rwa [hdel]
    · rwa [hdel]
    · rwa [hdel]
  rw [hhubCard] at hcount
  exact hcount.trans hboundaryCard


theorem gnIncident_arm_mem_outer_box
    {omega : ConfigSpace (Sym2 (Site 2))} {L N : ℕ} {j a : Site 2}
    (hc : bgf2_centre L j ∈ box 2 N)
    (hi : bc67_GnIncident omega L (bgf2_centre L j) a) :
    a ∈ box 2 (N + L + 1) := by
  obtain ⟨b, hb, hba⟩ := hi
  have hbrel : b - bgf2_centre L j ∈ box 2 L :=
    bc61_mem_boxAround.mp hb
  have hbbox : b ∈ box 2 (N + L) := by
    rw [mem_box] at hc hbrel ⊢
    intro i
    have htri : (b i).natAbs ≤ (bgf2_centre L j i).natAbs +
        (b i - bgf2_centre L j i).natAbs := by
      have hid : b i = bgf2_centre L j i +
          (b i - bgf2_centre L j i) := by ring
      calc
        (b i).natAbs = (bgf2_centre L j i +
            (b i - bgf2_centre L j i)).natAbs := congrArg Int.natAbs hid
        _ ≤ (bgf2_centre L j i).natAbs +
            (b i - bgf2_centre L j i).natAbs := Int.natAbs_add_le _ _
    have hc' := hc i
    have hb' : (b i - bgf2_centre L j i).natAbs ≤ L := by
      simpa only [Pi.sub_apply] using hbrel i
    omega
  exact arc_neighbour_in_box_succ hbbox hba.1


theorem faithfulAllOpenTrifAt_count_inner
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ)
    (J : Finset (Site 2))
    (htrif : ∀ j ∈ J, FaithfulAllOpenTrifAt omega L j)
    (hcenter : ∀ j ∈ J, bgf2_centre L j ∈ box 2 N) :
    J.card ≤ (vertexBoundary_finite 2 (N + L + 1)).toFinset.card := by
  apply faithfulAllOpenTrifAt_count_le_boundary omega L (N + L + 1)
    (by omega) J htrif
  intro j hj a hi _hinf
  exact gnIncident_arm_mem_outer_box (hcenter j hj) hi


theorem bgf2_centre_mem_scaled_box {L N : ℕ} {j : Site 2}
    (hj : j ∈ box 2 N) :
    bgf2_centre L j ∈ box 2 ((2 * L + 1) * N) := by
  rw [mem_box] at hj ⊢
  intro i
  simp only [bgf2_centre, Int.natAbs_mul]
  have hj' := hj i
  exact Nat.mul_le_mul_left (2 * L + 1) hj'

end StatMech.FrontierA
