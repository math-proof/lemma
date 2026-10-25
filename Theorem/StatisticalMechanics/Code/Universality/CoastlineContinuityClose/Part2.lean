/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineContinuityClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Def.StatisticalMechanics.Code.Universality.CoastlineContinuityClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem ccc_frontierRungsConnect_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hatom : ccc_FrontierReachesBottom ω n) : mbc_FrontierRungsConnect ω n := by
  obtain ⟨a₀, b₀, _ha0, _ha0', _hb0, _hb0', hanchor⟩ := hatom
  intro r hr0 hrn1 c c' hc hc'
  have hrn : r ≤ n := by omega
  have hr1_0 : (0 : ℤ) ≤ r + 1 := by omega
  have hr1_n : r + 1 ≤ n := by omega
  
  have hreachA : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  
  have hreachB : (pmd_boxFaceBarrier ω n).Reachable ![c', r + 1] ![a₀, b₀] :=
    hanchor (r + 1) hr1_0 hr1_n c' hc'
  
  have hrung : (pmd_boxFaceBarrier ω n).Adj ![c', (r + 1) - 1] ![c', r + 1] :=
    mbc_rung_vAdj ω n hr1_0 hr1_n hc'
  have hrung' : (pmd_boxFaceBarrier ω n).Adj ![c', r] ![c', r + 1] := by
    have he : (r + 1) - 1 = r := by ring
    rwa [he] at hrung
  
  have hreachB' : (pmd_boxFaceBarrier ω n).Reachable ![c', r] ![a₀, b₀] :=
    (hrung'.reachable).trans hreachB
  
  exact hreachA.trans hreachB'.symm


theorem ccc_reachesAnchor_of_frontierRungsConnect (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : mbc_FrontierRungsConnect ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  refine ⟨c₀, 0, hc₀.1, hc₀.2.1, by norm_num, hn, ?_⟩
  
  
  intro r hr0 hrn c hc
  
  
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr0
  
  have key : ∀ (k : ℕ), (k : ℤ) ≤ n → ∀ (ck : ℤ), mbc_IsRightFrontier ω n ck (k : ℤ) →
      (pmd_boxFaceBarrier ω n).Reachable ![c₀, (0 : ℤ)] ![ck, (k : ℤ)] := by
    intro k
    induction k with
    | zero =>
      intro _ ck hck
      
      
      
      have : ck = c₀ := ccc_rightFrontier_unique ω n hck hc₀
      subst this; exact Reachable.refl _
    | succ p ih =>
      intro hk ck hck
      have hp_n : (p : ℤ) ≤ n := by push_cast at hk ⊢; omega
      have hp_n1 : (p : ℤ) ≤ n - 1 := by push_cast at hk; omega
      obtain ⟨cp, hcp⟩ := mbc_exists_rightFrontier ω n hn hnoH (by positivity) hp_n
      have hih : (pmd_boxFaceBarrier ω n).Reachable ![c₀, (0 : ℤ)] ![cp, (p : ℤ)] :=
        ih hp_n cp hcp
      
      have hconn : (pmd_boxFaceBarrier ω n).Reachable ![cp, (p : ℤ)] ![ck, (p : ℤ)] := by
        have hck' : mbc_IsRightFrontier ω n ck ((p : ℤ) + 1) := by
          have hc : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [← hc]; exact hck
        exact hres (p : ℤ) (by positivity) hp_n1 cp ck hcp hck'
      have hrung : (pmd_boxFaceBarrier ω n).Adj ![ck, ((p : ℤ) + 1) - 1] ![ck, (p : ℤ) + 1] := by
        have hck' : mbc_IsRightFrontier ω n ck ((p : ℤ) + 1) := by
          have hc : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
          rw [← hc]; exact hck
        exact mbc_rung_vAdj ω n (by positivity) (by push_cast at hk; omega) hck'
      have hrung' : (pmd_boxFaceBarrier ω n).Adj ![ck, (p : ℤ)] ![ck, (p : ℤ) + 1] := by
        have he : ((p : ℤ) + 1) - 1 = (p : ℤ) := by ring
        rwa [he] at hrung
      have hcast : (((p : ℕ) + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      exact ((hih.trans hconn).trans hrung'.reachable)
  exact (key m hrn c hc).symm


theorem ccc_barrierConnectsRows_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) : pmd_BarrierConnectsRows ω n :=
  mbc_barrierConnectsRows_of_residue ω n hn hnoH
    (ccc_frontierRungsConnect_of_reachesBottom ω n hatom)


theorem ccc_faceDualVCrossing_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) : pmd_FaceDualVCrossing ω n :=
  mbc_faceDualVCrossing_of_residue ω n hn hnoH
    (ccc_frontierRungsConnect_of_reachesBottom ω n hatom)


theorem ccc_exhaustivity_of_reachesBottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hatom : ccc_FrontierReachesBottom ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (ccc_faceDualVCrossing_of_reachesBottom ω n hn hnoH hatom)


theorem ccc_wall_bottom_rung :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (0 : ℤ) - 1] :=
  ccc_frontierFace_down_adj bcc_wallCfg 2 (le_refl 0) (by norm_num)
    (mbc_wall_rightFrontier_at (le_refl 0) (by norm_num))


theorem ccc_wall_frontierReachesBottom : ccc_FrontierReachesBottom bcc_wallCfg 2 := by
  refine ⟨0, -1, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro r hr0 hrn c hc
  
  have hc0 : c = 0 := mbc_wall_rightFrontier_zero hc
  subst hc0
  
  
  
  
  have step : ∀ s : ℤ, 0 ≤ s → s ≤ 2 →
      (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, s - 1] ![0, s] :=
    fun s hs0 hs2 =>
      mbc_rung_vAdj bcc_wallCfg 2 hs0 hs2 (mbc_wall_rightFrontier_at hs0 hs2)
  
  have hbot : (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![0, (0 : ℤ)] ![0, (-1 : ℤ)] := by
    have h := ccc_wall_bottom_rung
    have he : ((0 : ℤ) - 1) = (-1 : ℤ) := by ring
    rw [he] at h
    exact h.reachable
  
  have h1 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (0 : ℤ)] ![0, (1 : ℤ)] := by
    have h := step 1 (by norm_num) (by norm_num)
    have he : ((1 : ℤ) - 1) = (0 : ℤ) := by ring
    rw [he] at h; exact h
  
  have h2 : (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, (1 : ℤ)] ![0, (2 : ℤ)] := by
    have h := step 2 (by norm_num) (by norm_num)
    have he : ((2 : ℤ) - 1) = (1 : ℤ) := by ring
    rw [he] at h; exact h
  
  interval_cases r
  · exact hbot
  · exact (h1.symm.reachable).trans hbot
  · exact ((h2.symm.reachable).trans (h1.symm.reachable)).trans hbot


theorem ccc_wall_frontierRungsConnect : mbc_FrontierRungsConnect bcc_wallCfg 2 :=
  ccc_frontierRungsConnect_of_reachesBottom bcc_wallCfg 2 ccc_wall_frontierReachesBottom


theorem ccc_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 :=
  ccc_barrierConnectsRows_of_reachesBottom bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    ccc_wall_frontierReachesBottom


theorem ccc_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ccc_faceDualVCrossing_of_reachesBottom bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    ccc_wall_frontierReachesBottom


theorem ccc_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality
end StatMech
