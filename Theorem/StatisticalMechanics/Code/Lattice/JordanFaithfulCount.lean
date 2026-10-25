/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_whb_sup_edge (G : SimpleGraph (Site 2)) {p q f0 g0 : Site 2} (hpq : p ≠ q)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q)) :
    whb_faceRegion (G ⊔ edge p q) = (whb_faceRegion G).deleteEdges {s(f0, g0)} := by
  ext f g
  rw [whb_faceRegion_adj, deleteEdges_adj, whb_faceRegion_adj]
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, not_or, Set.mem_singleton_iff]
  have hmem : sharedPrimalEdge f g ∈ (edge p q).edgeSet ↔ sharedPrimalEdge f g = s(p, q) :=
    jsf_mem_edgeSet_edge hpq _
  constructor
  · rintro ⟨hadj, hnG, hnE⟩
    refine ⟨⟨hadj, hnG⟩, ?_⟩
    intro heq
    apply hnE
    have : sharedPrimalEdge f g = sharedPrimalEdge f0 g0 :=
      (jce_sharedPrimalEdge_inj hadj hfg).mp heq
    rw [hmem, this, hshared]
  · rintro ⟨⟨hadj, hnG⟩, hne⟩
    refine ⟨hadj, hnG, ?_⟩
    intro hE
    apply hne
    rw [hmem, ← hshared] at hE
    exact (jce_sharedPrimalEdge_inj hadj hfg).mpr hE


theorem jfc_whb_bot : whb_faceRegion (⊥ : SimpleGraph (Site 2)) = hypercubicLattice 2 := by
  ext f g
  rw [whb_faceRegion_adj, SimpleGraph.edgeSet_bot]
  simp


theorem jfc_sharedPrimalEdge_endpoint_not_box (R : ℕ) {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g)
    (hf : (f 0).natAbs ≥ R + 2 ∨ (f 1).natAbs ≥ R + 2) {v : Site 2}
    (hv : v ∈ sharedPrimalEdge f g) : v ∉ box 2 R := by
  intro hbox
  rw [mem_box] at hbox
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  unfold sharedPrimalEdge at hv
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0] at hv
    rw [Sym2.mem_iff] at hv
    have h0nat := hbox 0; have h1nat := hbox 1
    rcases hv with rfl | rfl <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0nat h1nat) <;> omega
  · rw [if_neg h0] at hv
    rw [Sym2.mem_iff] at hv
    have h0nat := hbox 0; have h1nat := hbox 1
    rcases hv with rfl | rfl <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0nat h1nat) <;> omega


theorem jfc_exterior_sharedEdge_not_mem (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2} (hf : f ∈ exterior 2 (R + 1))
    (hadj : (hypercubicLattice 2).Adj f g) : sharedPrimalEdge f g ∉ H.edgeSet := by
  intro hmem
  rw [mem_exterior] at hf
  obtain ⟨i, hi⟩ := hf
  have hfbig : (f 0).natAbs ≥ R + 2 ∨ (f 1).natAbs ≥ R + 2 := by
    fin_cases i
    · left; simpa using hi
    · right; simpa using hi
  
  obtain ⟨p, q, hpq_eq, _⟩ := sharedPrimalEdge_isLatticeEdge hadj
  rw [hpq_eq, SimpleGraph.mem_edgeSet] at hmem
  have hpsupp : p ∈ H.support := ⟨q, hmem⟩
  have hpbox : p ∈ box 2 R := hR _ hpsupp
  exact jfc_sharedPrimalEdge_endpoint_not_box R hadj hfbig (hpq_eq ▸ Sym2.mem_mk_left p q) hpbox


theorem jfc_whb_adj_of_exterior (H : SimpleGraph (Site 2)) (R : ℕ)
    (hR : ∀ v ∈ H.support, v ∈ box 2 R) {f g : Site 2}
    (hf : f ∈ exterior 2 (R + 1)) (hadj : (hypercubicLattice 2).Adj f g) :
    (whb_faceRegion H).Adj f g :=
  ⟨hadj, jfc_exterior_sharedEdge_not_mem H R hR hf hadj⟩


theorem jfc_whb_regionComponents_finite (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite) :
    Finite (whb_faceRegion H).ConnectedComponent := by
  classical
  obtain ⟨R, hR⟩ := finite_subset_box H.support (jei_support_finite H hfin)
  set RG := whb_faceRegion H with hRG
  set S : Set (Site 2) := box 2 (R + 1) ∪ {beacon 2 (R + 1)} with hS
  have hSfin : S.Finite := (box_finite 2 (R + 1)).union (Set.finite_singleton _)
  have hb_ext : beacon 2 (R + 1) ∈ exterior 2 (R + 1) := beacon_mem_exterior (R + 1) (by omega)
  have hExtMk : ∀ x : Site 2, x ∈ exterior 2 (R + 1) →
      RG.connectedComponentMk x = RG.connectedComponentMk (beacon 2 (R + 1)) := by
    intro x hx
    refine ConnectedComponent.sound ?_
    have hconn := box_exterior_connected (R + 1) (by omega) x (beacon 2 (R + 1)) hx hb_ext
    have hmap := hconn.map
      (⟨Subtype.val, ?_⟩ : ((hypercubicLattice 2).induce (exterior 2 (R + 1))) →g RG)
    · simpa using hmap
    · intro a b hab
      exact jfc_whb_adj_of_exterior H R (fun v hv => hR hv) a.2 hab
  rw [← Set.finite_univ_iff]
  refine Set.Finite.of_surjOn RG.connectedComponentMk ?_ hSfin
  intro c _
  obtain ⟨x, hx⟩ := Quot.exists_rep c
  by_cases hxbox : x ∈ box 2 (R + 1)
  · exact ⟨x, Or.inl hxbox, hx⟩
  · have hxext : x ∈ exterior 2 (R + 1) := by rw [exterior_eq_compl_box]; exact hxbox
    refine ⟨beacon 2 (R + 1), Or.inr rfl, ?_⟩
    show RG.connectedComponentMk (beacon 2 (R + 1)) = c
    rw [← hExtMk x hxext]; exact hx


theorem jfc_whb_pushGraph_regionComponents_finite (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Finite (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent :=
  jfc_whb_regionComponents_finite _ (jei_pushGraph_edgeSet_finite P K)


theorem jfc_flankingFaces {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q) :
    ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧ sharedPrimalEdge f0 g0 = s(p, q) := by
  have hpq' := hpq
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq'
  have hadjface : ∀ a b : ℤ, (hypercubicLattice 2).Adj (![a, b] : Site 2) ![a - 1, b] := by
    intro a b; rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hadjface2 : ∀ a b : ℤ, (hypercubicLattice 2).Adj (![a, b] : Site 2) ![a, b - 1] := by
    intro a b; rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  by_cases h0 : p 0 = q 0
  · have hcase : q 1 = p 1 + 1 ∨ q 1 = p 1 - 1 := by omega
    rcases hcase with h1 | h1
    · refine ⟨![p 0, p 1], ![p 0 - 1, p 1], hadjface _ _, ?_⟩
      rw [sharedPrimalEdge_left (p 0) (p 1)]; unfold faceCorner00 faceCorner01
      have e1 : (![p 0, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp
      have e2 : (![p 0, p 1 + 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2]
    · refine ⟨![p 0, q 1], ![p 0 - 1, q 1], hadjface _ _, ?_⟩
      rw [sharedPrimalEdge_left (p 0) (q 1)]; unfold faceCorner00 faceCorner01
      have e1 : (![p 0, q 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      have e2 : (![p 0, q 1 + 1] : Site 2) = p := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2, Sym2.eq_swap]
  · have hcase : q 0 = p 0 + 1 ∨ q 0 = p 0 - 1 := by omega
    have h1 : p 1 = q 1 := by omega
    rcases hcase with h0' | h0'
    · refine ⟨![p 0, p 1], ![p 0, p 1 - 1], hadjface2 _ _, ?_⟩
      rw [sharedPrimalEdge_bottom (p 0) (p 1)]; unfold faceCorner00 faceCorner10
      have e1 : (![p 0, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp
      have e2 : (![p 0 + 1, p 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2]
    · refine ⟨![q 0, p 1], ![q 0, p 1 - 1], hadjface2 _ _, ?_⟩
      rw [sharedPrimalEdge_bottom (q 0) (p 1)]; unfold faceCorner00 faceCorner10
      have e1 : (![q 0, p 1] : Site 2) = q := by funext i; fin_cases i <;> simp <;> omega
      have e2 : (![q 0 + 1, p 1] : Site 2) = p := by funext i; fin_cases i <;> simp <;> omega
      rw [e1, e2, Sym2.eq_swap]


theorem jfc_flankingEdge_present (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) {x y : P.V}
    (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) :
    s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P K)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
  refine ⟨hfg, ?_⟩
  rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
  rintro ⟨u, v, hKuv, hu, hv⟩
  have hux : u = x := P.emb.injective hu
  have hvy : v = y := P.emb.injective hv
  subst_vars
  exact hnotK hKuv


theorem jfc_whb_delete_dichotomy (G : SimpleGraph (Site 2)) {p q f0 g0 : Site 2}
    [Finite (whb_faceRegion G).ConnectedComponent]
    [Finite (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent]
    (hpq : p ≠ q) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hpres : s(f0, g0) ∈ (whb_faceRegion G).edgeSet) :
    (((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 →
        Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (whb_faceRegion G).ConnectedComponent) ∧
      (¬ ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 →
        Nat.card (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (whb_faceRegion G).ConnectedComponent + 1) := by
  classical
  set RG := whb_faceRegion G with hRG
  set RGdel := RG.deleteEdges {s(f0, g0)} with hRGdel_def
  have hRGdel : whb_faceRegion (G ⊔ edge p q) = RGdel :=
    jfc_whb_sup_edge G hpq hfg hshared
  haveI hfinDel : Finite RGdel.ConnectedComponent :=
    hRGdel ▸ (inferInstance : Finite (whb_faceRegion (G ⊔ edge p q)).ConnectedComponent)
  have hdecomp : RG = RGdel ⊔ edge f0 g0 := by
    rw [hRGdel_def]
    exact jsf_deleteEdges_sup_edge_eq RG f0 g0 hpres
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rw [hRGdel]
    have hkeep := jsf_card_components_sup_edge_keep RGdel (a := f0) (b := g0) hr
    conv_rhs => rw [hdecomp]
    exact hkeep.symm
  · rw [hRGdel]
    have hmerge := jsf_card_components_sup_edge_merge RGdel (a := f0) (b := g0) hr
    rw [hdecomp]
    omega


end Lattice
end StatMech
