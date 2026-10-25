/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Def.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem cac_atom_of_pinned (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : cac_FrontierReachesBottomAtAnchor ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  exact cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega) (h c₀ hc₀)


theorem cac_pinned_of_atom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (h : ccc_FrontierReachesBottom ω n) : cac_FrontierReachesBottomAtAnchor ω n := by
  obtain ⟨a₀, b₀, _, _, _, _, hanchor⟩ := h
  intro c₀ hc₀ r hr0 hrn c hc
  
  have h1 : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![a₀, b₀] := hanchor r hr0 hrn c hc
  
  have h2 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![a₀, b₀] :=
    hanchor 0 (le_refl 0) hn c₀ hc₀
  
  have h3 : (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![c₀, -1] :=
    cac_row0_frontier_reaches_bottom ω n hn hc₀
  
  exact (h1.trans h2.symm).trans h3


theorem cac_wall_frontierReachesBottomAtAnchor :
    cac_FrontierReachesBottomAtAnchor bcc_wallCfg 2 := by
  intro c₀ hc₀ r hr0 hrn c hc
  
  have hc₀0 : c₀ = 0 := mbc_wall_rightFrontier_zero hc₀
  subst hc₀0
  
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


theorem cac_wall_atom : ccc_FrontierReachesBottom bcc_wallCfg 2 :=
  cac_atom_of_pinned bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    cac_wall_frontierReachesBottomAtAnchor


theorem cac_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ccc_faceDualVCrossing_of_reachesBottom bcc_wallCfg 2 (by norm_num) bcc_noH_wall cac_wall_atom


theorem cac_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality
end StatMech
