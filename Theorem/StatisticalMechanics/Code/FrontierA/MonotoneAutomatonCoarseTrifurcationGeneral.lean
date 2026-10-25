/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem removeBox_siteForce_eq_general (d n : ℕ)
    (eta : ConfigSpace (Site d)) :
    removeSites (bc61_boxAround d n 0)
        (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) =
      removeSites (bc61_boxAround d n 0) (siteToBond eta) := by
  classical
  rw [bc61_boxAround_zero]
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      unfold removeSites
      by_cases hinc : ∃ t ∈ boxFinsetBK d n, t ∈ s(x, y)
      · rw [if_pos hinc, if_pos hinc]
      · rw [if_neg hinc, if_neg hinc]
        have hx : x ∉ boxFinsetBK d n := by
          intro hx
          exact hinc ⟨x, hx, by simp⟩
        have hy : y ∉ boxFinsetBK d n := by
          intro hy
          exact hinc ⟨y, hy, by simp⟩
        simp [siteToBond_mk, forceSitesOccupied_apply, hx, hy]


theorem siteToBond_le_siteForce_general (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    siteToBond eta ≤
      siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
  apply siteToBond_mono
  intro x
  by_cases hx : x ∈ boxFinsetBK d n <;>
    simp [forceSitesOccupied_apply, hx]


theorem siteForce_bgfdIndexAllOpen (n : ℕ)
    (eta : ConfigSpace (Site d)) :
    BgfdIndexAllOpen
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  intro x y hx hy _hadj
  have hxbox : x ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hx
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  have hybox : y ∈ box d n := by
    have h := bgfd_idx_iff_inBox.mp hy
    rw [bgfd_centre_zero] at h
    simpa [bgfdInBox] using h
  simp [siteToBond_mk, forceSitesOccupied_apply,
    mem_boxFinsetBK_iff.mpr hxbox, mem_boxFinsetBK_iff.mpr hybox]


theorem coarseTrif_siteForce_of_coarse_general (n : ℕ)
    (eta : ConfigSpace (Site d))
    (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
    bc61_IsCoarseTrifurcation
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  obtain ⟨a₁, a₂, a₃, hi₁, hi₂, hi₃, hinf, hcut⟩ := h
  have hmono := siteToBond_le_siteForce_general n eta
  refine ⟨a₁, a₂, a₃, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨b, hb, hba⟩ := hi₁
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₂
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · obtain ⟨b, hb, hba⟩ := hi₃
    exact ⟨b, hb, openSubgraph_mono hmono hba⟩
  · simpa only [removeBox_siteForce_eq_general] using hinf
  · simpa only [removeBox_siteForce_eq_general] using hcut


theorem shell_of_walk_into_box_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {b u x : Site d}
    (w : (openSubgraph d omega).Walk u x) :
    Connected d (removeSites (bc61_boxAround d L 0) omega) b u →
      u ∉ bc61_boxAround d L 0 → x ∈ bc61_boxAround d L 0 →
      ∃ s t : Site d, (openSubgraph d omega).Adj s t ∧
        t ∈ bc61_boxAround d L 0 ∧
        Connected d (removeSites (bc61_boxAround d L 0) omega) b s := by
  induction w with
  | nil =>
      intro _ hu hx
      exact absurd hx hu
  | @cons u v z hadj w' ih =>
      intro hbu hu hx
      by_cases hv : v ∈ bc61_boxAround d L 0
      · exact ⟨u, v, hadj, hv, hbu⟩
      · have hstep : Connected d
            (removeSites (bc61_boxAround d L 0) omega) u v :=
          bc117_cut_step_of_notMem hadj hu hv
        exact ih (hbu.trans hstep) hv hx


theorem attach_of_meetsBox_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {x x' : Site d}
    (hinf : (cluster d omega x).Infinite)
    (hx'box : x' ∈ bc61_boxAround d L 0)
    (hxx' : cluster d omega x = cluster d omega x') :
    ∃ a : Site d,
      (∃ bx ∈ bc61_boxAround d L 0, (openSubgraph d omega).Adj bx a) ∧
      (cluster d (removeSites (bc61_boxAround d L 0) omega) a).Infinite ∧
      cluster d omega x = cluster d omega a := by
  classical
  obtain ⟨b, hbconn, hbnot, hbinf⟩ :=
    bc117_boxAvoiding_external_infinite omega hinf (bc61_boxAround d L 0)
  have hxx'conn : Connected d omega x x' := by
    have hx'mem : x' ∈ cluster d omega x := by
      rw [hxx']
      exact self_mem_cluster omega x'
    exact mem_cluster.mp hx'mem
  have hbx' : Connected d omega b x' := hbconn.symm.trans hxx'conn
  obtain ⟨w⟩ := hbx'
  obtain ⟨s, t, hadj, htbox, hscut⟩ :=
    shell_of_walk_into_box_general (b := b) w
      (connected_refl _ b) hbnot hx'box
  refine ⟨s, ⟨t, htbox, hadj.symm⟩, ?_, ?_⟩
  · have hcl : cluster d (removeSites (bc61_boxAround d L 0) omega) b =
        cluster d (removeSites (bc61_boxAround d L 0) omega) s :=
      cluster_eq_of_connected hscut
    rwa [hcl] at hbinf
  · have hbs : Connected d omega b s := bc61_connected_of_cut hscut
    exact cluster_eq_of_connected (hbconn.trans hbs)


theorem coarseTrif_of_three_meetBox_general {L : ℕ}
    {omega : ConfigSpace (Sym2 (Site d))} {x₁ x₂ x₃ : Site d}
    (hi₁ : (cluster d omega x₁).Infinite)
    (hi₂ : (cluster d omega x₂).Infinite)
    (hi₃ : (cluster d omega x₃).Infinite)
    (hd₁₂ : cluster d omega x₁ ≠ cluster d omega x₂)
    (hd₁₃ : cluster d omega x₁ ≠ cluster d omega x₃)
    (hd₂₃ : cluster d omega x₂ ≠ cluster d omega x₃)
    (hb₁ : x₁ ∈ bc61_boxAround d L 0)
    (hb₂ : x₂ ∈ bc61_boxAround d L 0)
    (hb₃ : x₃ ∈ bc61_boxAround d L 0) :
    bc61_IsCoarseTrifurcation omega L 0 := by
  obtain ⟨a₁, hadj₁, hinf₁, he₁⟩ :=
    attach_of_meetsBox_general hi₁ hb₁ rfl
  obtain ⟨a₂, hadj₂, hinf₂, he₂⟩ :=
    attach_of_meetsBox_general hi₂ hb₂ rfl
  obtain ⟨a₃, hadj₃, hinf₃, he₃⟩ :=
    attach_of_meetsBox_general hi₃ hb₃ rfl
  have hda₁₂ : cluster d omega a₁ ≠ cluster d omega a₂ := by
    rw [← he₁, ← he₂]
    exact hd₁₂
  have hda₁₃ : cluster d omega a₁ ≠ cluster d omega a₃ := by
    rw [← he₁, ← he₃]
    exact hd₁₃
  have hda₂₃ : cluster d omega a₂ ≠ cluster d omega a₃ := by
    rw [← he₂, ← he₃]
    exact hd₂₃
  exact ⟨a₁, a₂, a₃, hadj₁, hadj₂, hadj₃,
    ⟨hinf₁, hinf₂, hinf₃⟩,
    bc115_disconnected_of_distinctClusters _ omega hda₁₂,
    bc115_disconnected_of_distinctClusters _ omega hda₁₃,
    bc115_disconnected_of_distinctClusters _ omega hda₂₃⟩


theorem siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox
    (eta : ConfigSpace (Site d)) (n : ℕ)
    (h : siteToBond eta ∈ threeMeetBox d n) :
    BgfdFaithfulAllOpenTrifAt
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
  obtain ⟨_htop, x₁, x₂, x₃, hb₁, hb₂, hb₃,
    hi₁, hi₂, hi₃, hd₁₂, hd₁₃, hd₂₃⟩ := h
  have hb₁' : x₁ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₁
  have hb₂' : x₂ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₂
  have hb₃' : x₃ ∈ bc61_boxAround d n 0 := by
    rw [bc61_boxAround_zero]
    exact mem_boxFinsetBK_iff.mpr hb₃
  have hcoarse : bc61_IsCoarseTrifurcation (siteToBond eta) n 0 :=
    coarseTrif_of_three_meetBox_general hi₁ hi₂ hi₃
      hd₁₂ hd₁₃ hd₂₃ hb₁' hb₂' hb₃'
  refine ⟨?_, siteForce_bgfdIndexAllOpen n eta⟩
  rw [bgfd_centre_zero]
  exact (bc67_coarseTrif_is_G_n_trifurcation _ n 0).mp
    (coarseTrif_siteForce_of_coarse_general n eta hcoarse)


end StatMech.FrontierA
