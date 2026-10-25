/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part6
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem sampledGrid_eq {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) {k : ℕ} (hk : k ≤ N) :
    sampledGrid n N hN gamma k = gridFloor n (gamma (sampleTime N k hk hN)) := by
  simp [sampledGrid, Nat.min_eq_left hk]

theorem sampledGrid_zero {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) : sampledGrid n N hN gamma 0 = gridFloor n p := by
  rw [sampledGrid_eq n N hN gamma (Nat.zero_le N), sampleTime_zero, Path.source]

theorem sampledGrid_self {p q : Fin 2 → ℝ} (n N : ℕ) (hN : 0 < N)
    (gamma : Path p q) : sampledGrid n N hN gamma N = gridFloor n q := by
  rw [sampledGrid_eq n N hN gamma (le_refl N), sampleTime_self, Path.target]


theorem exists_fine_sampling {p q : Fin 2 → ℝ} (gamma : Path p q)
    {n : ℕ} (hn : 0 < n) :
    ∃ N : ℕ, ∃ hN : 0 < N, ∀ (k : ℕ) (hk : k < N),
      dist (gamma (sampleTime N k hk.le hN))
        (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ) := by
  have heps : 0 < 1 / (n : ℝ) := by positivity
  obtain ⟨delta, hdelta, hgamma⟩ :=
    (Metric.uniformContinuous_iff.mp gamma.uniformContinuous) _ heps
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hdelta
  let N := m + 1
  have hN : 0 < N := by simp [N]
  refine ⟨N, hN, ?_⟩
  intro k hk
  apply hgamma
  rw [dist_sampleTime_succ N k hk hN]
  simpa [N] using hm


theorem sampledGrid_walk_near {p q : Fin 2 → ℝ} (gamma : Path p q)
    {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (hfine : ∀ (k : ℕ) (hk : k < N),
      dist (gamma (sampleTime N k hk.le hN))
        (gamma (sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN)) < 1 / (n : ℝ))
    {z : Site 2} (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
    ∃ t : unitInterval, dist (gridEmbed n z) (gamma t) < 3 / (n : ℝ) := by
  rcases gridWalk_mem_support_cases (sampledGrid n N hN gamma) N z hz with h | ⟨k, hk, hzk⟩
  · refine ⟨0, ?_⟩
    rw [h, sampledGrid_zero, Path.source]
    exact gridFloor_near hn p
  · let tk := sampleTime N k hk.le hN
    let tk1 := sampleTime N (k + 1) (Nat.succ_le_iff.2 hk) hN
    have hgk : sampledGrid n N hN gamma k = gridFloor n (gamma tk) :=
      sampledGrid_eq n N hN gamma hk.le
    have hgk1 : sampledGrid n N hN gamma (k + 1) = gridFloor n (gamma tk1) :=
      sampledGrid_eq n N hN gamma (Nat.succ_le_iff.2 hk)
    refine ⟨tk, ?_⟩
    rw [hgk, hgk1] at hzk
    exact gridConnector_near hn (hfine k hk) hzk

theorem sampledGrid_walk_mem_rect {p q : Fin 2 → ℝ} (gamma : Path p q)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    {n N : ℕ} (hN : 0 < N) {z : Site 2}
    (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  apply gridWalk_mem_rect (N := N) (g := sampledGrid n N hN gamma) _ hz
  intro k hk
  rw [sampledGrid_eq n N hN gamma hk]
  rw [mem_rect]
  have hp : InUnitSquare (gamma (sampleTime N k hk hN)) :=
    hgamma ⟨_, rfl⟩
  exact ⟨gridFloor_coord_nonneg hp 0,
    gridFloor_coord_le hp 0,
    gridFloor_coord_nonneg hp 1,
    gridFloor_coord_le hp 1⟩

theorem gridFloor_coord_eq_zero {n : ℕ} {p : Fin 2 → ℝ} {i : Fin 2}
    (h : p i = 0) : gridFloor n p i = 0 := by
  simp [gridFloor, h]

theorem gridFloor_coord_eq_nat {n : ℕ} {p : Fin 2 → ℝ} {i : Fin 2}
    (h : p i = 1) : gridFloor n p i = (n : ℤ) := by
  simp [gridFloor, h]


theorem sampled_grid_walks_intersect
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    (heta : Set.range eta ⊆ {x | InUnitSquare x})
    (hl0 : hl 0 = 0) (hr0 : hr 0 = 1)
    (vb1 : vb 1 = 0) (vt1 : vt 1 = 1)
    {n NH NV : ℕ} (hn : 0 < n) (hNH : 0 < NH) (hNV : 0 < NV) :
    ∃ z : Site 2,
      z ∈ (gridWalk (sampledGrid n NH hNH gamma) NH).support ∧
      z ∈ (gridWalk (sampledGrid n NV hNV eta) NV).support := by
  let H := gridWalk (sampledGrid n NH hNH gamma) NH
  let V0 := gridWalk (sampledGrid n NV hNV eta) NV
  let a0 := gridFloor n vb 0
  let b0 := gridFloor n vt 0
  have hVsrc : sampledGrid n NV hNV eta 0 = ![a0, 0] := by
    rw [sampledGrid_zero]
    funext i
    fin_cases i
    · rfl
    · simpa using gridFloor_coord_eq_zero (n := n) vb1
  have hVtgt : sampledGrid n NV hNV eta NV = ![b0, (n : ℤ)] := by
    rw [sampledGrid_self]
    funext i
    fin_cases i
    · rfl
    · simpa using gridFloor_coord_eq_nat (n := n) vt1
  let V : (hypercubicLattice 2).Walk ![a0, 0] ![b0, (n : ℤ)] :=
    V0.copy hVsrc hVtgt
  have hVBox0 : ∀ z ∈ V0.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact sampledGrid_walk_mem_rect eta heta hNV hz
  have hVBox : ∀ z ∈ V.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact hVBox0 z (by simpa [V] using hz)
  have ha0lo : 0 ≤ a0 := gridFloor_coord_nonneg (heta ⟨0, by simp⟩) 0
  have ha0hi : a0 ≤ (n : ℤ) := gridFloor_coord_le (heta ⟨0, by simp⟩) 0
  have hb0lo : 0 ≤ b0 := gridFloor_coord_nonneg (heta ⟨1, by simp⟩) 0
  have hb0hi : b0 ≤ (n : ℤ) := gridFloor_coord_le (heta ⟨1, by simp⟩) 0
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hsep : ArcSeparatingSet {z : Site 2 | z ∈ V.support}
      0 (n : ℤ) 0 (n : ℤ) :=
    jec_arcSeparatingSet 0 (n : ℤ) 0 (n : ℤ) a0 b0 hnZ hnZ.le
      ha0lo ha0hi hb0lo hb0hi V hVBox _ (fun _ h ↦ h)
  have hHBox : ∀ z ∈ H.support, z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
    intro z hz
    exact sampledGrid_walk_mem_rect gamma hgamma hNH hz
  have hHsrc : (sampledGrid n NH hNH gamma 0) 0 = 0 := by
    rw [sampledGrid_zero]
    exact gridFloor_coord_eq_zero hl0
  have hHtgt : (sampledGrid n NH hNH gamma NH) 0 = (n : ℤ) := by
    rw [sampledGrid_self]
    exact gridFloor_coord_eq_nat hr0
  obtain ⟨z, hzH, hzV⟩ := tpc_two_paths_cross_of_sep hsep
    (hHBox _ H.start_mem_support) (hHBox _ H.end_mem_support)
    hHsrc hHtgt H hHBox
  refine ⟨z, ?_, ?_⟩
  · exact hzH
  · simpa [V] using hzV


theorem unitSquare_paths_intersect
    {hl hr vb vt : Fin 2 → ℝ}
    (gamma : Path hl hr) (eta : Path vb vt)
    (hgamma : Set.range gamma ⊆ {x | InUnitSquare x})
    (heta : Set.range eta ⊆ {x | InUnitSquare x})
    (hl0 : hl 0 = 0) (hr0 : hr 0 = 1)
    (vb1 : vb 1 = 0) (vt1 : vt 1 = 1) :
    ∃ t s : unitInterval, gamma t = eta s := by
  by_contra hdisj
  have hgammaCompact : IsCompact (Set.range gamma) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image gamma.continuous)
  have hetaCompact : IsCompact (Set.range eta) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image eta.continuous)
  have hrangeDisj : Disjoint (Set.range gamma) (Set.range eta) := by
    rw [Set.disjoint_left]
    intro x hx hxeta
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨s, hs⟩ := hxeta
    exact hdisj ⟨t, s, hs.symm⟩
  obtain ⟨rho, hrho, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hgammaCompact hetaCompact.isClosed hrangeDisj
  have hrhoR : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hrho
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (div_pos hrhoR (by norm_num : (0 : ℝ) < 6))
  let n := m + 1
  have hn : 0 < n := by simp [n]
  have hmesh : 6 / (n : ℝ) < (rho : ℝ) := by
    calc
      6 / (n : ℝ) = 6 * (1 / (n : ℝ)) := by ring
      _ < 6 * ((rho : ℝ) / 6) := mul_lt_mul_of_pos_left (by simpa [n] using hm) (by norm_num)
      _ = (rho : ℝ) := by ring
  obtain ⟨NH, hNH, hfineH⟩ := exists_fine_sampling gamma hn
  obtain ⟨NV, hNV, hfineV⟩ := exists_fine_sampling eta hn
  obtain ⟨z, hzH, hzV⟩ := sampled_grid_walks_intersect gamma eta hgamma heta
    hl0 hr0 vb1 vt1 hn hNH hNV
  obtain ⟨t, ht⟩ := sampledGrid_walk_near gamma hn hNH hfineH hzH
  obtain ⟨s, hs⟩ := sampledGrid_walk_near eta hn hNV hfineV hzV
  have hrtsE : (rho : ENNReal) < edist (gamma t) (eta s) :=
    hsep (gamma t) ⟨t, rfl⟩ (eta s) ⟨s, rfl⟩
  have hrts : (rho : ℝ) < dist (gamma t) (eta s) := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top
      (edist_ne_top (gamma t) (eta s))).2 hrtsE
    simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
  have hclose : dist (gamma t) (eta s) < 6 / (n : ℝ) := by
    calc
      dist (gamma t) (eta s) ≤
          dist (gamma t) (gridEmbed n z) + dist (gridEmbed n z) (eta s) :=
        dist_triangle _ _ _
      _ < 3 / (n : ℝ) + 3 / (n : ℝ) :=
        add_lt_add (by rw [_root_.dist_comm]; exact ht) hs
      _ = 6 / (n : ℝ) := by ring
  linarith


end ContinuousRectangleCrossing
end StatMech
