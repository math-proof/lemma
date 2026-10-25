/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MengerBarrierClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Def.StatisticalMechanics.Code.Universality.MengerBarrierClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mbc_rightFrontier_succ_notMem (ω : ConfigSpace (Sym2 (Site 2))) (n c r : ℤ)
    (h : mbc_IsRightFrontier ω n c r) : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n := by
  obtain ⟨hc0, hcn, _hcL, hmax⟩ := h
  exact hmax (c + 1) (by omega) (by omega)


theorem mbc_exists_rightFrontier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    ∃ c : ℤ, mbc_IsRightFrontier ω n c r := by
  classical
  have h0L : (![0, r] : Site 2) ∈ bcd_leftReach ω n := by
    apply jex_leftSide_subset_leftReach
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by simp [hn], by simpa using hr0, by simpa using hrn⟩
  have hnL : (![n, r] : Site 2) ∉ bcd_leftReach ω n := by
    apply jex_rightSide_notin_leftReach ω n hnoH
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  let S : Finset ℤ := (Finset.Icc 0 n).filter (fun c => (![c, r] : Site 2) ∈ bcd_leftReach ω n)
  have h0mem : (0 : ℤ) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨le_refl 0, hn⟩, h0L⟩
  obtain ⟨c, hcS, hcmax⟩ := S.exists_max_image id ⟨0, h0mem⟩
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hcS
  obtain ⟨⟨hc0, hcn⟩, hcL⟩ := hcS
  have hcltn : c < n := by
    rcases lt_or_eq_of_le hcn with h | h
    · exact h
    · subst h; exact absurd hcL hnL
  refine ⟨c, hc0, by omega, hcL, ?_⟩
  intro c' hcc' hc'n hc'L
  have hmem : c' ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hc'n⟩, hc'L⟩
  have := hcmax c' hmem; simp only [id] at this; omega


theorem mbc_rung_vAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (pmd_boxFaceBarrier ω n).Adj ![c, r - 1] ![c, r] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := htr
  have hc1 : (![c + 1, r] : Site 2) ∉ bcd_leftReach ω n :=
    mbc_rightFrontier_succ_notMem ω n c r ⟨hc0, hcn, hcL, _hmax⟩
  have hface : (![c, r] : Site 2) = ![c, (r - 1) + 1] := by funext i; fin_cases i <;> simp
  rw [pmd_boxFaceBarrier_adj]
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![c, r], ![c + 1, r], ?_, ?_, ?_, ?_⟩
  · rw [hface, sharedPrimalEdge_top]
    unfold faceCorner01 faceCorner11
    have hrr : (r - 1) + 1 = r := by ring
    rw [hrr]
  · rw [bdEdge_mk]; exact ⟨fun _ hcontra => hc1 hcontra, fun _ => hcL⟩
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩


end Universality
end StatMech
