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
import Def.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mbc_reach_to_row (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : mbc_FrontierRungsConnect ω n)
    {c0 : ℤ} (h0 : mbc_IsRightFrontier ω n c0 0) :
    ∀ (k : ℕ), (k : ℤ) ≤ n →
      ∃ ck : ℤ, mbc_IsRightFrontier ω n ck (k : ℤ) ∧
        (pmd_boxFaceBarrier ω n).Reachable ![c0, -1] ![ck, (k : ℤ)] := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨c0, h0, ?_⟩
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![c0, (0 : ℤ) - 1] ![c0, (0 : ℤ)] :=
      mbc_rung_vAdj ω n (le_refl 0) hn h0
    simpa using hrung.reachable
  | succ m ih =>
    intro hk
    have hm : (m : ℤ) ≤ n := by push_cast at hk ⊢; omega
    obtain ⟨cm, hcm, hreachm⟩ := ih hm
    have hm1_0 : (0 : ℤ) ≤ ((m : ℤ) + 1) := by positivity
    have hm1_n : ((m : ℤ) + 1) ≤ n := by push_cast at hk; omega
    obtain ⟨cm1, hcm1⟩ := mbc_exists_rightFrontier ω n hn hnoH hm1_0 hm1_n
    have hconn : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, (m : ℤ)] := by
      have hmle : (m : ℤ) ≤ n - 1 := by omega
      exact hres (m : ℤ) (by positivity) hmle cm cm1 hcm hcm1
    have hrung : (pmd_boxFaceBarrier ω n).Adj ![cm1, ((m : ℤ) + 1) - 1] ![cm1, ((m : ℤ) + 1)] :=
      mbc_rung_vAdj ω n hm1_0 hm1_n hcm1
    have hrung' : (pmd_boxFaceBarrier ω n).Adj ![cm1, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] := by
      have he : ((m : ℤ) + 1) - 1 = (m : ℤ) := by ring
      rwa [he] at hrung
    refine ⟨cm1, ?_, ?_⟩
    · have hc : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hc]; exact hcm1
    · have hstep : (pmd_boxFaceBarrier ω n).Reachable ![cm, (m : ℤ)] ![cm1, ((m : ℤ) + 1)] :=
        hconn.trans hrung'.reachable
      have hcast : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hcast]; exact hreachm.trans hstep


theorem mbc_barrierConnectsRows_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_BarrierConnectsRows ω n := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  obtain ⟨c0, hc0⟩ := mbc_exists_rightFrontier ω (m : ℤ) hn hnoH (le_refl 0) (by positivity)
  obtain ⟨cn, hcn, hreach⟩ := mbc_reach_to_row ω (m : ℤ) hn hnoH hres hc0 m (le_refl _)
  exact ⟨c0, cn, hc0.1, hc0.2.1, hcn.1, hcn.2.1, hreach⟩


theorem mbc_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    pmd_FaceDualVCrossing ω n :=
  pmd_faceDualVCrossing_of_residue ω n (mbc_barrierConnectsRows_of_residue ω n hn hnoH hres)


theorem mbc_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hres : mbc_FrontierRungsConnect ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (mbc_faceDualVCrossing_of_residue ω n hn hnoH hres)


theorem mbc_wall_rightFrontier_zero {c r : ℤ} (h : mbc_IsRightFrontier bcc_wallCfg 2 c r) :
    c = 0 := by
  obtain ⟨_hc0, _hcn, hcL, _hmax⟩ := h
  simpa using rdv_leftReach_wall_x0 hcL


theorem mbc_wall_frontierRungsConnect : mbc_FrontierRungsConnect bcc_wallCfg 2 := by
  intro r _hr0 _hrn c c' hc hc'
  have e1 : c = 0 := mbc_wall_rightFrontier_zero hc
  have e2 : c' = 0 := mbc_wall_rightFrontier_zero hc'
  subst e1; subst e2
  exact Reachable.refl _


theorem mbc_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 :=
  mbc_barrierConnectsRows_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect


theorem mbc_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  mbc_faceDualVCrossing_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    mbc_wall_frontierRungsConnect


theorem mbc_residue_atom_single_step (ω : ConfigSpace (Sym2 (Site 2))) (n r c c' : ℤ)
    (h : c = c') : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c', r] := by
  subst h; exact Reachable.refl _


theorem mbc_wall_rightFrontier_at {r : ℤ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    mbc_IsRightFrontier bcc_wallCfg 2 0 r := by
  refine ⟨le_refl 0, by norm_num, ?_, ?_⟩
  · apply jex_leftSide_subset_leftReach
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp, by norm_num, by simpa using hr0, by simpa using hr2⟩
  · intro c' _hc' hc'2 hc'L
    have := rdv_leftReach_wall_x0 hc'L
    simp at this; omega


theorem mbc_wall_bottom_rung_real :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ) - 1] ![0, (0 : ℤ)] :=
  mbc_rung_vAdj bcc_wallCfg 2 (le_refl 0) (by norm_num)
    (mbc_wall_rightFrontier_at (le_refl 0) (by norm_num))


theorem mbc_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality
end StatMech
