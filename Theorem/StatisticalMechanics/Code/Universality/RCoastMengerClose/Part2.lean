/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RCoastMengerClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Def.StatisticalMechanics.Code.Universality.RCoastMengerClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem rcm_rCoastConnected_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (hall : rcm_RCoastConnectedAll ω n) :
    bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  have hfront : bac_IsRCoastFace ω n ![c₀, 0] :=
    bac_frontierFace_isRCoast ω n hnoH (le_refl 0) (by omega) hc₀
  exact hall f ![c₀, 0] hf hfront


theorem rcm_all_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : rcm_RCoastConnectedAll ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  intro f g hf hg
  exact (hres c₀ hc₀ f hf).trans (hres c₀ hc₀ g hg).symm


theorem rcm_reachesBottom_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : ccc_FrontierReachesBottom ω n :=
  bac_reachesBottom_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)


theorem rcm_frontierArcReaches_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : crc2_FrontierArcReaches ω n :=
  bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)


theorem rcm_faceDualVCrossing_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) : pmd_FaceDualVCrossing ω n :=
  bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH (rcm_rCoastConnected_of_all ω n hnoH hall)


theorem rcm_exhaustivity_of_all (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hall : rcm_RCoastConnectedAll ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (rcm_faceDualVCrossing_of_all ω n hn hnoH hall)


theorem rcm_wall_RCoastConnectedAll : rcm_RCoastConnectedAll bcc_wallCfg 2 := by
  intro f g hf hg
  obtain ⟨gf, hgf⟩ := hf.1
  obtain ⟨gg, hgg⟩ := hg.1
  obtain ⟨hf0, hf1⟩ := bac_wall_barrierFace_col0 hgf
  obtain ⟨hg0, hg1⟩ := bac_wall_barrierFace_col0 hgg
  have hfe : f = ![0, f 1] := by funext i; fin_cases i <;> simp [hf0]
  have hge : g = ![0, g 1] := by funext i; fin_cases i <;> simp [hg0]
  rw [hfe, hge]
  exact (bac_wall_col0_reaches_origin (by tauto)).trans
    (bac_wall_col0_reaches_origin (by tauto)).symm


theorem rcm_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  rcm_frontierArcReaches_of_all bcc_wallCfg 2 (by norm_num) bcc_noH_wall rcm_wall_RCoastConnectedAll


theorem rcm_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  rcm_faceDualVCrossing_of_all bcc_wallCfg 2 (by norm_num) bcc_noH_wall rcm_wall_RCoastConnectedAll


theorem rcm_wall_rightComplement_connected :
    ∃ (huc : (![1, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2)
      (hvc : (![2, 0] : Site 2) ∈ bac_boxMinusL bcc_wallCfg 2),
      ((hypercubicLattice 2).induce (bac_boxMinusL bcc_wallCfg 2)).Reachable
        ⟨![1, 0], huc⟩ ⟨![2, 0], hvc⟩ := by
  have hg := bac_wall_gap_mem
  have hwall : (![2, 0] : Site 2) ∈ bac_rightComplement bcc_wallCfg 2 :=
    bac_rightWall_mem_rightComplement bcc_wallCfg 2 bcc_noH_wall (by norm_num) (by norm_num)
  exact rcm_rightComplement_connected_pair bcc_wallCfg 2 bcc_noH_wall hg hwall


theorem rcm_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall

end Universality
end StatMech
