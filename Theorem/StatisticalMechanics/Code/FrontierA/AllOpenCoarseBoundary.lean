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
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


theorem bgf2_deleted_reachable_of_cut_connected
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ}
    (h0 : bgf2_IndexAllOpen omega L 0) {a b : Site 2}
    (h : Connected 2 (removeSites (bc61_boxAround 2 L 0) omega) a b) :
    (bkg_deleteVertex (bgf2_Gf omega L) 0).Reachable
      (bgf2_q omega L a) (bgf2_q omega L b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons x z b hadj p ih =>
    refine Reachable.trans ?_ ih
    have hxout : x ∉ bc61_boxAround 2 L 0 := by
      intro hx
      exact stac_removeSites_no_neighbor (bc61_boxAround 2 L 0) omega hx hadj
    have hzout : z ∉ bc61_boxAround 2 L 0 := by
      intro hz
      exact stac_removeSites_no_neighbor (bc61_boxAround 2 L 0) omega hz hadj.symm
    have hx0 : bgf2_q omega L x ≠ 0 := by
      intro hx
      exact hxout ((bgf2_q_eq_zero_iff_mem h0).1 hx)
    have hz0 : bgf2_q omega L z ≠ 0 := by
      intro hz
      exact hzout ((bgf2_q_eq_zero_iff_mem h0).1 hz)
    by_cases heq : bgf2_q omega L x = bgf2_q omega L z
    · rw [heq]
    · apply SimpleGraph.Adj.reachable
      rw [bkg_deleteVertex_adj]
      refine ⟨?_, hx0, hz0⟩
      rw [bgf2_Gf_adj]
      exact ⟨heq, x, z, rfl, rfl,
        openSubgraph_mono (daep_removeSites_le (bc61_boxAround 2 L 0) omega) hadj⟩


theorem bgf2_q_eq_centre_iff
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j x : Site 2}
    (hj : bgf2_IndexAllOpen omega L j) :
    bgf2_q omega L x = bgf2_centre L j ↔ bgn_idx L x = j := by
  unfold bgf2_q
  by_cases hP : bgf2_IndexAllOpen omega L (bgn_idx L x)
  · rw [if_pos hP]
    constructor
    · exact bgf2_centre_inj
    · intro h
      rw [h]
  · rw [if_neg hP]
    constructor
    · intro h
      exfalso
      apply hP
      have hidx : bgn_idx L x = j := by rw [h, bgf2_idx_centre]
      rwa [hidx]
    · intro h
      exfalso
      apply hP
      rwa [h]


theorem bgf2_mem_box_centre_iff {L : ℕ} {j x : Site 2} :
    x ∈ bc61_boxAround 2 L (bgf2_centre L j) ↔ bgn_idx L x = j := by
  rw [bc61_mem_boxAround, bgf2_idx_iff_inBox]
  simp only [mem_box, bgf2_inBox, Pi.sub_apply]


theorem bgf2_indexAllOpen_cut_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j k : Site 2}
    (hk : bgf2_IndexAllOpen omega L k) (hkj : k ≠ j) :
    bgf2_IndexAllOpen
      (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) L k := by
  intro x y hx hy hadj
  have hxout : x ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hin
    apply hkj
    rw [← hx]
    exact bgf2_mem_box_centre_iff.mp hin
  have hyout : y ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
    intro hin
    apply hkj
    rw [← hy]
    exact bgf2_mem_box_centre_iff.mp hin
  rw [bc61_removeBox_apply_of_notMem hxout hyout]
  exact hk x y hx hy hadj


theorem bgf2_cut_q_eq_connected_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j a b : Site 2}
    (hj : bgf2_IndexAllOpen omega L j)
    (h : bgf2_q omega L a = bgf2_q omega L b)
    (hne : bgf2_q omega L a ≠ bgf2_centre L j) :
    Connected 2
      (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
  have hja : bgn_idx L a ≠ j := fun hidx =>
    hne ((bgf2_q_eq_centre_iff hj).2 hidx)
  unfold bgf2_q at h
  by_cases hPa : bgf2_IndexAllOpen omega L (bgn_idx L a)
  · rw [if_pos hPa] at h
    by_cases hPb : bgf2_IndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      have hidx := bgf2_centre_inj h
      exact bgf2_indexAllOpen_connected
        (bgf2_indexAllOpen_cut_at hPa hja) rfl hidx.symm
    · rw [if_neg hPb] at h
      exfalso
      apply hPb
      have hbi : bgn_idx L b = bgn_idx L a := by
        rw [← h, bgf2_idx_centre]
      rwa [hbi]
  · rw [if_neg hPa] at h
    by_cases hPb : bgf2_IndexAllOpen omega L (bgn_idx L b)
    · rw [if_pos hPb] at h
      exfalso
      apply hPa
      have hai : bgn_idx L a = bgn_idx L b := by
        rw [h, bgf2_idx_centre]
      rwa [hai]
    · rw [if_neg hPb] at h
      rw [h]


theorem bgf2_cut_connected_of_reach_at
    {omega : ConfigSpace (Sym2 (Site 2))} {L : ℕ} {j : Site 2}
    (hj : bgf2_IndexAllOpen omega L j) :
    ∀ {u v : Site 2},
      (bkg_deleteVertex (bgf2_Gf omega L) (bgf2_centre L j)).Reachable u v →
      ∀ a b, bgf2_q omega L a = u → bgf2_q omega L b = v →
        u ≠ bgf2_centre L j → v ≠ bgf2_centre L j →
        Connected 2
          (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a b := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    intro a b ha hb hu hv
    exact bgf2_cut_q_eq_connected_at hj (ha.trans hb.symm)
      (by rw [ha]; exact hu)
  | @cons u z v hadj p ih =>
    intro a b ha hb hu hv
    obtain ⟨⟨huz, a', b', ha', hb', hab'⟩, hune, hzne⟩ := hadj
    have h1 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a a' :=
      bgf2_cut_q_eq_connected_at hj (ha.trans ha'.symm)
        (by rw [ha]; exact hu)
    have ha'out : a' ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
      rw [bgf2_mem_box_centre_iff, ← bgf2_q_eq_centre_iff hj]
      rw [ha']
      exact hune
    have hb'out : b' ∉ bc61_boxAround 2 L (bgf2_centre L j) := by
      rw [bgf2_mem_box_centre_iff, ← bgf2_q_eq_centre_iff hj]
      rw [hb']
      exact hzne
    have h2 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) a' b' :=
      bc61_cut_adj_connected hab'.1 hab'.2 ha'out hb'out
    have h3 : Connected 2
        (removeSites (bc61_boxAround 2 L (bgf2_centre L j)) omega) b' b :=
      ih b' b hb' hb hzne hv
    exact (h1.trans h2).trans h3


end StatMech.FrontierA
