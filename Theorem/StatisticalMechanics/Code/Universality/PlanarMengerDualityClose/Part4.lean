/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarMengerDualityClose.lean -/

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
import Def.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem pmd_faceDualVCrossing_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pmd_BarrierConnectsRows ω n) : pmd_FaceDualVCrossing ω n := by
  obtain ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach⟩ := h
  exact ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach.mono (pmd_boxFaceBarrier_le_faceOpenDual ω n)⟩


theorem pmd_contour_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle :=
  fdd_leftReach_dualCircuit ω n hn hnoH


theorem pmd_exhaustivity_of_residue (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : pmd_BarrierConnectsRows ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ pmd_FaceDualVCrossing ω n :=
  Or.inr (pmd_faceDualVCrossing_of_residue ω n h)


theorem pmd_wall_faceVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (fci_faceOpenDual bcc_wallCfg).Adj ![0, b] ![0, b + 1] := by
  apply pmd_faceVAdj_of_closed
  simp only [bcc_wallCfg]
  rcases hb with rfl | rfl | rfl <;> decide


theorem pmd_wall_faceDualVCrossing : pmd_FaceDualVCrossing bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_faceVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_faceVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_faceVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3


theorem pmd_wall_barrierVAdj {b : ℤ} (hb : b = -1 ∨ b = 0 ∨ b = 1) :
    (pmd_boxFaceBarrier bcc_wallCfg 2).Adj ![0, b] ![0, b + 1] := by
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ![0, b + 1], ![1, b + 1],
    ?_, ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; rfl
  · rw [bdEdge_mk]
    constructor
    · intro _
      exact fun hc => by
        have := rdv_leftReach_wall_x0 hc; simp at this
    · intro hno
      exact jex_leftSide_subset_leftReach bcc_wallCfg 2
        ⟨by rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp, by simp⟩
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp
  · rw [mem_rect]; rcases hb with rfl | rfl | rfl <;> simp


theorem pmd_wall_barrierConnectsRows : pmd_BarrierConnectsRows bcc_wallCfg 2 := by
  refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have h1 := (pmd_wall_barrierVAdj (b := -1) (by tauto)).reachable
  have h2 := (pmd_wall_barrierVAdj (b := 0) (by tauto)).reachable
  have h3 := (pmd_wall_barrierVAdj (b := 1) (by tauto)).reachable
  norm_num at h1 h2 h3 ⊢
  exact (h1.trans h2).trans h3


theorem pmd_wall_faceDualV_via_residue : pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  pmd_faceDualVCrossing_of_residue bcc_wallCfg 2 pmd_wall_barrierConnectsRows


theorem pmd_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall


theorem pmd_wall_noH_yet_faceDualV :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧ pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, pmd_wall_faceDualVCrossing⟩


theorem pmd_wall_only_face_frame_works :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 ∧
      pmd_FaceDualVCrossing bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH, pmd_wall_faceDualVCrossing⟩

end Universality
end StatMech
