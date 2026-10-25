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
import Def.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jkd_r0_ne_r1 : jkd_r0 ≠ jkd_r1 := by decide


theorem jkd_ring_centre_deg4 : jkd_gr9G.neighborSet 4 = {1, 3, 5, 7} := by
  ext j; rw [SimpleGraph.mem_neighborSet, jkd_gr9G_adj]; fin_cases j <;> simp [jkd_gr9rel]


theorem jkd_ring_Gadj : jkd_ringP.G.Adj jkd_r0 jkd_r1 := by
  change jkd_gr9G.Adj jkd_r0 jkd_r1; rw [jkd_gr9G_adj]; decide

theorem jkd_ring_emb0 : jkd_ringP.emb jkd_r0 = ![0, 0] := rfl

theorem jkd_ring_emb1 : jkd_ringP.emb jkd_r1 = ![1, 0] := rfl


theorem jkd_ring_shared_bottom :
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) := by
  rw [jkd_ring_emb0, jkd_ring_emb1,
    show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
  unfold faceCorner00 faceCorner10; norm_num


theorem jkd_ring_witness_reach :
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  set wall := s(![(0:ℤ), 0], ![(0:ℤ), -1]) with hwall
  have mkAdj : ∀ a b : Site 2, (hypercubicLattice 2).Adj a b → s(a, b) ≠ wall →
      ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj a b := by
    intro a b hlat hne
    rw [deleteEdges_adj, Set.mem_singleton_iff]
    exact ⟨jkd_faceRegion_botPush_adj jkd_ringP hlat, hne⟩
  have e1 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), 0] ![(1:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {wall}).Adj
      ![(1:ℤ), -1] ![(0:ℤ), -1] :=
    mkAdj _ _ (jkd_latadj (by rw [Fin.sum_univ_two]; norm_num))
      (by rw [hwall, ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact e1.reachable.trans (e2.reachable.trans e3.reachable)


theorem jkd_keepResidue_witness_ring :
    (⊥ : SimpleGraph jkd_ringP.V) ≤ jkd_ringP.G ∧
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (⊥ : SimpleGraph jkd_ringP.V).Reachable jkd_r0 jkd_r1 ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  refine ⟨bot_le, jkd_ring_Gadj, ?_, ?_, jkd_ring_shared_bottom, ?_, jkd_ring_witness_reach⟩
  · rw [SimpleGraph.bot_adj]; exact not_false
  · exact jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  · intro h; rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h


theorem jkd_keepResidue_witness_ring_consistent (hres : whc_WhitneyColoringResidue) :
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hkeep := jkd_keepResidue_of_windingColoring hres jkd_ringP
  have hna : ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] :=
    jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnr : ¬ (⊥ : SimpleGraph jkd_ringP.V).Reachable jkd_r0 jkd_r1 := by
    intro h; rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h
  exact hkeep ⊥ bot_le jkd_ring_Gadj hna hfg jkd_ring_shared_bottom hnr

end Lattice
end StatMech
