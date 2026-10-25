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
import Instance.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jed_nbr_adj (v : Site 2) (i : Fin 4) : (hypercubicLattice 2).Adj v (jce_nbr v i) := by
  fin_cases i <;>
    · simp only [jce_nbr]
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num


theorem jed_jce_degree_primalGraph (E : Set (Sym2 (Site 2))) (v : Site 2) :
    jce_degree (jed_primalGraph E).edgeSet v = jce_degree E v := by
  classical
  rw [jce_degree, jce_degree]
  congr 1
  apply Finset.filter_congr
  intro i _
  have : (s(v, jce_nbr v i) ∈ (jed_primalGraph E).edgeSet) ↔ (s(v, jce_nbr v i) ∈ E) := by
    rw [SimpleGraph.mem_edgeSet]; exact ⟨fun h => h.2, fun h => ⟨jed_nbr_adj v i, h⟩⟩
  simp only [this]


theorem jed_degree_primalGraph (E : Set (Sym2 (Site 2))) (v : Site 2) :
    (jed_primalGraph E).degree v = jce_degree E v := by
  rw [← jed_jce_degree_primalGraph E v, jeb_jce_degree_eq_degree (jed_primalGraph E)
    (jed_primalGraph_le E) v]


theorem jed_wall_mem_cutSet (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    sharedPrimalEdge f0 g0 ∈
      jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) := by
  rw [jed_mem_cutSet_iff _ hfg]
  exact ⟨fun _ => hsep, fun _ => Reachable.refl f0⟩


theorem jed_cutSet_subset (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hfg : (hypercubicLattice 2).Adj f0 g0) :
    jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) ⊆
      insert (sharedPrimalEdge f0 g0) H.edgeSet := by
  rintro e ⟨a, b, hab, rfl, hsplit⟩
  have hnotadj : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b := by
    intro hadj
    have : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 a ↔
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 b :=
      ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    tauto
  by_cases hwall : s(a, b) = s(f0, g0)
  · rw [(jce_sharedPrimalEdge_inj hab hfg).mp hwall]; exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    rw [deleteEdges_adj, Set.mem_singleton_iff, not_and_or, not_not] at hnotadj
    rcases hnotadj with hnwhb | hw
    · rw [whb_faceRegion_adj, not_and_or] at hnwhb
      rcases hnwhb with hnl | hns
      · exact absurd hab hnl
      · rw [not_not] at hns; exact hns
    · exact absurd hw hwall


theorem jed_cutMinusWall_degree_data (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2)
    (hpq : (hypercubicLattice 2).Adj p q) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    Odd (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) p) ∧
      Odd (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) q) ∧
      (∀ v, v ≠ p → v ≠ q → Even (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) v)) := by
  classical
  set T := fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v with hT
  set E := jed_cutSet T with hE
  set E' := E \ {s(p, q)} with hE'
  
  have hwallE : s(p, q) ∈ E := by
    rw [hE, ← hshared]; exact jed_wall_mem_cutSet H f0 g0 hfg hsep
  have hwallnE' : s(p, q) ∉ E' := fun h => h.2 rfl
  have hinsert : insert (s(p, q)) E' = E := by
    rw [hE', Set.insert_diff_singleton, Set.insert_eq_self.mpr hwallE]
  
  have hEeven : ∀ v, Even (jce_degree E v) := fun v => jed_cutSet_even T v
  have hqp : s(q, p) ∉ E' := fun h => hwallnE' (by rwa [Sym2.eq_swap] at h)
  refine ⟨?_, ?_, ?_⟩
  · have hd := jeb_jce_degree_insert_endpoint E' p q hpq hwallnE'
    rw [hinsert] at hd
    have := hEeven p; rw [hd, Nat.even_add_one, Nat.not_even_iff_odd] at this; exact this
  · have hd := jeb_jce_degree_insert_endpoint E' q p hpq.symm hqp
    rw [show s(q, p) = s(p, q) from Sym2.eq_swap, hinsert] at hd
    have := hEeven q; rw [hd, Nat.even_add_one, Nat.not_even_iff_odd] at this; exact this
  · intro v hvp hvq
    have hd := jeb_jce_degree_insert_other E' p q v hvp hvq
    rw [hinsert] at hd
    have := hEeven v; rwa [hd] at this


theorem jed_reachable_of_separated (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (_hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    H.Reachable p q := by
  classical
  set T := fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v with hT
  set E := jed_cutSet T with hE
  set E' := E \ {s(p, q)} with hE'
  set K := jed_primalGraph E' with hK
  
  have hEsub : E ⊆ insert (sharedPrimalEdge f0 g0) H.edgeSet := jed_cutSet_subset H f0 g0 hfg
  rw [hshared] at hEsub
  have hE'sub : E' ⊆ H.edgeSet := by
    intro e he
    rcases hEsub he.1 with h | h
    · exact absurd (h ▸ Set.mem_singleton _ : e ∈ ({s(p, q)} : Set _)) he.2
    · exact h
  
  have hKleH : K ≤ H := by
    intro u w hadj
    have hmem : s(u, w) ∈ E' := hadj.2
    exact (SimpleGraph.mem_edgeSet H).mp (hE'sub hmem)
  
  have hHsupp : H.support.Finite := by
    haveI : Fintype H.edgeSet := hfin.fintype
    exact jeb_support_finite_of_edgeSet H
  have hKsuppSub : K.support ⊆ H.support := by
    intro v hv
    rw [SimpleGraph.mem_support] at hv ⊢
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hKleH hw⟩
  have hKsupp : K.support.Finite := hHsupp.subset hKsuppSub
  
  obtain ⟨hop, hoq, hoth⟩ :=
    jed_cutMinusWall_degree_data H p q f0 g0 hpq hfg hshared hsep
  have hdeg : ∀ v, K.degree v = jce_degree E' v := fun v => jed_degree_primalGraph E' v
  have hKp : Odd (K.degree p) := by rw [hdeg]; exact hop
  have hKq : Odd (K.degree q) := by rw [hdeg]; exact hoq
  have hKoth : ∀ v, v ≠ p → v ≠ q → Even (K.degree v) := by
    intro v hvp hvq; rw [hdeg]; exact hoth v hvp hvq
  
  have hKreach : K.Reachable p q := jeb_two_odd_reachable K hKsupp p q hKp hKq hKoth
  exact hKreach.mono hKleH


theorem jed_finiteKeepReconnect : jkr_FiniteKeepReconnectResidue := by
  intro H p q f0 g0 hfin hpq hnpq hfg hshared hnr
  by_contra hsep
  exact hnr (jed_reachable_of_separated H hfin p q f0 g0 hpq hnpq hfg hshared hsep)


theorem jed_sameComponentResidue : jfd_SameComponentResidue :=
  jfd_sameComponent_iff_finiteKeep.mpr jed_finiteKeepReconnect


theorem jed_keepResidue (P : PlanarZ2Subgraph) : jwc_KeepResidue P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared hnr
  have hfin : (jei_pushGraph P K).edgeSet.Finite := jei_pushGraph_edgeSet_finite P K
  have hpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet :=
    jkd_wall_not_mem_pushGraph P K hnotK
  have hnrpush : ¬ (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) := by
    rw [jei_push_reachable_iff]; exact hnr
  exact jed_finiteKeepReconnect (jei_pushGraph P K) (P.emb x) (P.emb y) f0 g0
    hfin hpq hnpq hfg hshared hnrpush


theorem jed_faithfulDiscreteJordan (P : PlanarZ2Subgraph) : whc_FaithfulDiscreteJordan P :=
  jwc_faithfulDiscreteJordan_of_keepResidue P (jed_keepResidue P)


theorem jed_not_reachable_of_isolated (H : SimpleGraph (Site 2)) (u v : Site 2)
    (hiso : ∀ w, ¬ H.Adj u w) (hne : u ≠ v) : ¬ H.Reachable u v := by
  rintro ⟨w⟩
  cases w with
  | nil => exact hne rfl
  | cons hadj _ => exact hiso _ hadj


end Lattice
end StatMech
