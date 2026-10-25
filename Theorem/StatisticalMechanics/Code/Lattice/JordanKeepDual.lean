/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanKeepDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jkd_wall_not_mem_pushGraph (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hnotK : ¬ K.Adj x y) :
    s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst hux; subst hvy
  exact hnotK hKuv


theorem jkd_keepResidue_of_windingColoring (hres : whc_WhitneyColoringResidue)
    (P : PlanarZ2Subgraph) : jwc_KeepResidue P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared hnr
  
  have hpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet :=
    jkd_wall_not_mem_pushGraph P K hnotK
  obtain ⟨φ, hcut, htrack, hback⟩ :=
    hres (jei_pushGraph P K) (P.emb x) (P.emb y) f0 g0 hpq hnpq hfg hshared
  
  have hnrPush : ¬ (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) := by
    rw [jei_push_reachable_iff]; exact hnr
  
  have hsame : (φ f0 ↔ φ g0) := by
    by_contra hdiff
    exact hnrPush (htrack.mpr hdiff)
  
  exact hback hsame


theorem jkd_faithfulDiscreteJordan_of_windingColoring (hres : whc_WhitneyColoringResidue)
    (P : PlanarZ2Subgraph) : whc_FaithfulDiscreteJordan P :=
  jwc_faithfulDiscreteJordan_of_keepResidue P (jkd_keepResidue_of_windingColoring hres P)


theorem jkd_latadj {a b : Site 2} (h : (∑ i, (a i - b i).natAbs) = 1) :
    (hypercubicLattice 2).Adj a b := by rw [hypercubicLattice_adj]; exact h


theorem jkd_faceRegion_botPush_adj (P : PlanarZ2Subgraph) {a b : Site 2}
    (hlat : (hypercubicLattice 2).Adj a b) :
    (whb_faceRegion (jei_pushGraph P ⊥)).Adj a b := by
  rw [whb_faceRegion_adj, jei_pushGraph_bot]
  refine ⟨hlat, ?_⟩
  rw [SimpleGraph.edgeSet_bot]
  exact fun h => h


theorem jkd_shared_bottom :
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) := by
  rw [jbc_Pce_emb0, jbc_Pce_emb1,
    show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
  unfold faceCorner00 faceCorner10; norm_num


theorem jkd_witness_square_reach :
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set wall := s(![(0:ℤ), 0], ![(0:ℤ), -1]) with hwall
  
  have mkAdj : ∀ a b : Site 2, (hypercubicLattice 2).Adj a b → s(a, b) ≠ wall →
      ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj a b := by
    intro a b hlat hne
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨jkd_faceRegion_botPush_adj jbc_Pce hlat, hne⟩
  have e1 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)


theorem jkd_keepResidue_witness_square :
    
    (⊥ : SimpleGraph jbc_Pce.V) ≤ jbc_Pce.G ∧
    
    jbc_Pce.G.Adj jbc_v0 jbc_v1 ∧
    
    ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 ∧
    
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jbc_Pce.emb jbc_v0, jbc_Pce.emb jbc_v1) ∧
    
    ¬ (⊥ : SimpleGraph jbc_Pce.V).Reachable jbc_v0 jbc_v1 ∧
    
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  refine ⟨bot_le, jbc_Pce_Gadj, ?_, ?_, jkd_shared_bottom, ?_, jkd_witness_square_reach⟩
  · rw [SimpleGraph.bot_adj]; exact not_false
  · exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  · 
    intro h
    rw [SimpleGraph.reachable_bot] at h
    exact jbc_v0_ne_v1 h


theorem jkd_keepResidue_witness_consistent (hres : whc_WhitneyColoringResidue) :
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hkeep := jkd_keepResidue_of_windingColoring hres jbc_Pce
  have hna : ¬ (⊥ : SimpleGraph jbc_Pce.V).Adj jbc_v0 jbc_v1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnr : ¬ (⊥ : SimpleGraph jbc_Pce.V).Reachable jbc_v0 jbc_v1 := by
    intro h; rw [SimpleGraph.reachable_bot] at h; exact jbc_v0_ne_v1 h
  exact hkeep ⊥ bot_le jbc_Pce_Gadj hna hfg jkd_shared_bottom hnr


end Lattice
end StatMech
