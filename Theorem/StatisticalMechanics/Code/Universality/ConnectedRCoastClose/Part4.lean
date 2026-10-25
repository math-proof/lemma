/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part3
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_frontierFace_interfaceSideWith (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c₀ : ℤ}
    (hc₀ : mbc_IsRightFrontier ω n c₀ 0) :
    crr_InterfaceSideWith ω n ![c₀, 0] ![c₀ + 1, 0] := by
  obtain ⟨hc0, hcn, hcL, _hmax⟩ := id hc₀
  have hgapR : (![c₀ + 1, 0] : Site 2) ∈ bac_rightComplement ω n :=
    bac_gap_mem_rightComplement ω n hnoH (le_refl 0) hn hc₀
  refine ⟨hgapR, ![c₀, 0], hcL, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · rw [mem_rect]; exact ⟨by simpa using hc0, by simp; omega, by simp, by simpa using hn⟩
  · rw [mem_rect]; exact ⟨by simp; omega, by simp; omega, by simp, by simpa using hn⟩
  · left; simp
  · right; left; simp


theorem crr_rCoastConnected_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : bac_RCoastConnected ω n := by
  intro c₀ hc₀ f hf
  
  have hfront : crr_InterfaceSideWith ω n ![c₀, 0] ![c₀ + 1, 0] :=
    crr_frontierFace_interfaceSideWith ω n hn hnoH hc₀
  
  obtain ⟨qf, hqf⟩ := crr_rCoastFace_interfaceSideWith ω n hf
  
  have hqfR : qf ∈ bac_rightComplement ω n := hqf.1
  have hgapR : (![c₀ + 1, 0] : Site 2) ∈ bac_rightComplement ω n := hfront.1
  
  obtain ⟨hqfc, hgapc, hreach⟩ :=
    rcm_rightComplement_connected_pair ω n hnoH hqfR hgapR
  
  exact hres f ![c₀, 0] qf ![c₀ + 1, 0] hqf hfront hqfc hgapc hreach


theorem crr_frontierArcReaches_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : crc2_FrontierArcReaches ω n :=
  bac_frontierArcReaches_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)


theorem crr_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : pmd_FaceDualVCrossing ω n :=
  bac_faceDualVCrossing_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)


theorem crr_reachesBottom_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) : ccc_FrontierReachesBottom ω n :=
  bac_reachesBottom_of_rCoastConnected ω n hn hnoH
    (crr_rCoastConnected_of_residue ω n hn hnoH hres)


theorem crr_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : crr_InterfaceCoastConnected ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (crr_faceDualVCrossing_of_residue ω n hn hnoH hres)


theorem crr_residue_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : crr_InterfaceCoastConnected ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  intro f₁ f₂ q₁ q₂ h1 h2 _ _ _
  
  have hr1 : bac_IsRCoastFace ω n f₁ := by
    refine ⟨crr_hasInterfaceSide_pmdVertex ω n (crr_hasInterfaceSide_of_with ω n h1), q₁, h1.1, ?_⟩
    obtain ⟨_, _, _, _, _, _, hqc⟩ := h1; tauto
  have hr2 : bac_IsRCoastFace ω n f₂ := by
    refine ⟨crr_hasInterfaceSide_pmdVertex ω n (crr_hasInterfaceSide_of_with ω n h2), q₂, h2.1, ?_⟩
    obtain ⟨_, _, _, _, _, _, hqc⟩ := h2; tauto
  exact (hres c₀ hc₀ f₁ hr1).trans (hres c₀ hc₀ f₂ hr2).symm


theorem crr_wall_interfaceCoastConnected : crr_InterfaceCoastConnected bcc_wallCfg 2 := by
  intro f₁ f₂ q₁ q₂ h1 h2 _ _ _
  
  have hr1 : ∃ g : Site 2, (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f₁ g :=
    crr_hasInterfaceSide_pmdVertex bcc_wallCfg 2 (crr_hasInterfaceSide_of_with bcc_wallCfg 2 h1)
  have hr2 : ∃ g : Site 2, (pmd_boxFaceBarrier bcc_wallCfg 2).Adj f₂ g :=
    crr_hasInterfaceSide_pmdVertex bcc_wallCfg 2 (crr_hasInterfaceSide_of_with bcc_wallCfg 2 h2)
  obtain ⟨g1, hg1⟩ := hr1
  obtain ⟨g2, hg2⟩ := hr2
  obtain ⟨hf10, hf11⟩ := bac_wall_barrierFace_col0 hg1
  obtain ⟨hf20, hf21⟩ := bac_wall_barrierFace_col0 hg2
  have hfe1 : f₁ = ![0, f₁ 1] := by funext i; fin_cases i <;> simp [hf10]
  have hfe2 : f₂ = ![0, f₂ 1] := by funext i; fin_cases i <;> simp [hf20]
  rw [hfe1, hfe2]
  exact (bac_wall_col0_reaches_origin (by tauto)).trans
    (bac_wall_col0_reaches_origin (by tauto)).symm


theorem crr_wall_frontierArcReaches : crc2_FrontierArcReaches bcc_wallCfg 2 :=
  crr_frontierArcReaches_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected


theorem crr_wall_rCoastConnected : bac_RCoastConnected bcc_wallCfg 2 :=
  crr_rCoastConnected_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected


theorem crr_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  crr_faceDualVCrossing_of_residue bcc_wallCfg 2 (by norm_num) bcc_noH_wall
    crr_wall_interfaceCoastConnected


theorem crr_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall


end Universality
end StatMech
