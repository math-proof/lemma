/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Def.StatisticalMechanics.Code.Lattice.WindingColoring.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem wcl_empty_instance_valid :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true]
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num


theorem wcl_cutFlip_bot_iff (a b : Site 2) :
    wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔
      s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  unfold wcl_cutFlip whc_isCross
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, false_or, or_false]


theorem wcl_squareLoop_flipCount :
    wcl_flipCount (wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1])
      wcl_squareLoop = 1 := by
  classical
  set flip := wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] with hflip
  unfold wcl_squareLoop
  
  rw [wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons, wcl_flipCount_cons,
    wcl_flipCount_nil]
  
  rw [if_pos (Or.inl (by
    rw [hflip, wcl_cutFlip_bot_iff]))]
  
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]
  
  rw [if_neg (by
    rintro (h | h) <;> · rw [hflip, wcl_cutFlip_bot_iff] at h
                         rw [Sym2.eq_iff] at h
                         simp only [site2_eq] at h
                         omega)]


theorem wcl_whitneyColoringResidue_false : ¬ whc_WhitneyColoringResidue := by
  intro hres
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := wcl_empty_instance_valid
  obtain ⟨φ, hcut, _, _⟩ :=
    hres (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
      hpq hnpq hfg hshared
  refine wcl_no_cutColoring_of_odd_loop (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1]
    wcl_squareLoop ?_ ⟨φ, hcut⟩
  rw [wcl_squareLoop_flipCount]
  decide


theorem wcl_faceRegion_bot_adj (a b : Site 2) :
    (whb_faceRegion (⊥ : SimpleGraph (Site 2))).Adj a b ↔ (hypercubicLattice 2).Adj a b := by
  rw [whb_faceRegion_adj]
  simp only [SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true, and_true]


theorem wcl_faceRegion_bot_reconnect :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set G := (whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
    {s(![(0:ℤ), 0], ![(0:ℤ), -1])} with hG
  have mk : ∀ u v : Site 2, (hypercubicLattice 2).Adj u v →
      s(u, v) ≠ s(![(0:ℤ), 0], ![(0:ℤ), -1]) → G.Adj u v := by
    intro u v hadj hne
    rw [hG, deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨(wcl_faceRegion_bot_adj u v).mpr hadj, hne⟩
  have e1 : G.Adj ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  have e2 : G.Adj ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  have e3 : G.Adj ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mk _ _ (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num)
      (by rw [ne_eq, Sym2.eq_iff]; simp only [site2_eq]; norm_num)
  exact (e1.reachable.trans e2.reachable).trans e3.reachable


theorem wcl_deleted_separated_of_closedEven (H : SimpleGraph (Site 2)) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  set φ := wcl_windingColoring (wcl_cutFlip H f0 g0) f0 with hφ
  have hcut : whc_CutColoring H f0 g0 φ :=
    wcl_windingColoring_isCutColoring H f0 g0 hce f0
  
  have hflank : ¬ (φ f0 ↔ φ g0) := by
    have := hcut f0 g0 hfg
    have hmark : whc_isCross H f0 g0 ∨ s(f0, g0) = s(f0, g0) := Or.inr rfl
    rw [this] at hmark
    tauto
  exact whc_deleted_separated H f0 g0 φ hcut hflank


end Lattice
end StatMech
