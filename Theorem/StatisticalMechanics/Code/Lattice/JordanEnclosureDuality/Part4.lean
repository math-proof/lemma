/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jed_boxH_iso_p (w : Site 2) : ¬ jed_boxH.Adj ![(0:ℤ), 0] w := by
  rw [jed_boxH, jed_primalGraph_adj]
  rintro ⟨_, hmem⟩
  rw [Finset.mem_coe] at hmem
  simp only [jed_boxEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, site2_eq] at hmem
  omega


theorem jed_boxH_iso_q (w : Site 2) : ¬ jed_boxH.Adj ![(1:ℤ), 0] w := by
  rw [jed_boxH, jed_primalGraph_adj]
  rintro ⟨_, hmem⟩
  rw [Finset.mem_coe] at hmem
  simp only [jed_boxEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, site2_eq] at hmem
  omega


theorem jed_boxH_edgeSet_finite : jed_boxH.edgeSet.Finite :=
  (jed_boxEdges.finite_toSet).subset (jed_primalGraph_edgeSet_subset _)


theorem jed_enclosingBox_witness :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jed_boxH.edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ jed_boxH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion jed_boxH).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hpq : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hshared : sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
    rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  have hnpq : s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jed_boxH.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; exact jed_boxH_iso_p _
  have hnr : ¬ jed_boxH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    jed_not_reachable_of_isolated jed_boxH _ _ jed_boxH_iso_p (by
      rw [ne_eq, site2_eq]; norm_num)
  refine ⟨hpq, hnpq, hfg, hshared, hnr, ?_⟩
  exact jed_finiteKeepReconnect jed_boxH ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
    jed_boxH_edgeSet_finite hpq hnpq hfg hshared hnr


theorem jed_witnesses :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion jed_boxH).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    jkr_lineH.edgeSet.Infinite :=
  ⟨(jkr_witness_bot).2.2.2.2.2, (jkr_witness_square).2.2.2.2.2,
    (jkr_witness_ring).2.2.2.2.2, jed_enclosingBox_witness.2.2.2.2.2,
    jkr_lineH_edgeSet_infinite⟩


theorem jed_status :
    (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧
    jkr_FiniteKeepReconnectResidue ∧
    jfd_SameComponentResidue ∧
    (∀ P : PlanarZ2Subgraph, whc_FaithfulDiscreteJordan P) :=
  ⟨jed_cutSet_even, jed_finiteKeepReconnect, jed_sameComponentResidue, jed_faithfulDiscreteJordan⟩

end Lattice
end StatMech
