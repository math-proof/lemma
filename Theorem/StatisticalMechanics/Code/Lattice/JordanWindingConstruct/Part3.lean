/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepDual.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwn_keepReconnect_of_whitneyColoring (hres : whc_WhitneyColoringResidue) :
    jwn_KeepReconnectResidue := by
  intro H p q f0 g0 hpq hnpq hfg hshared hnr
  obtain ⟨φ, _hcut, htrack, hback⟩ := hres H p q f0 g0 hpq hnpq hfg hshared
  have hsame : (φ f0 ↔ φ g0) := by
    by_contra hdiff; exact hnr (htrack.mpr hdiff)
  exact hback hsame


theorem jwn_witness_square :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  obtain ⟨hpq, hnpq, hfg, hshared⟩ := jwn_bot_instance_valid
  refine ⟨hpq, hnpq, hfg, hshared, ?_, jwn_bot_reconnect⟩
  intro h; rw [SimpleGraph.reachable_bot] at h
  simp only [site2_eq] at h; omega


theorem jwn_witness_ring :
    jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧
    s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧
    ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
        {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hna : ¬ (⊥ : SimpleGraph jkd_ringP.V).Adj jkd_r0 jkd_r1 := by
    rw [SimpleGraph.bot_adj]; exact not_false
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] :=
    jkd_latadj (by rw [Fin.sum_univ_two]; norm_num)
  have hnpq : s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉
      (jei_pushGraph jkd_ringP ⊥).edgeSet := jkd_wall_not_mem_pushGraph jkd_ringP ⊥ hna
  have hnr : ¬ (jei_pushGraph jkd_ringP ⊥).Reachable
      (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) := by
    rw [jei_push_reachable_iff]; intro h
    rw [SimpleGraph.reachable_bot] at h; exact jkd_r0_ne_r1 h
  exact ⟨jkd_ring_Gadj, hnpq, hfg, jkd_ring_shared_bottom, hnr, jkd_ring_witness_reach⟩


theorem jwn_status :
    ¬ whc_WhitneyColoringResidue ∧
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    (whc_WhitneyColoringResidue → jwn_KeepReconnectResidue) :=
  ⟨jwn_whitneyColoringResidue_false, jwn_bot_reconnect, jwn_keepReconnect_of_whitneyColoring⟩

end Lattice
end StatMech
