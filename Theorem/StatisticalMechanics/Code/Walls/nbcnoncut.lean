/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Def.StatisticalMechanics.Code.Walls.nbcnoncut
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem nbc_induce_adj_of_latticeOn {K : Set (Site 2)} {x y : Site 2}
    (hx : x ∈ K) (hy : y ∈ K) (h : (latticeOn K).Adj x y) :
    ((hypercubicLattice 2).induce K).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [SimpleGraph.induce_adj]; exact h.1


theorem nbc_induce_reachable_of_latticeOn {K : Set (Site 2)} :
    ∀ {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K),
      (latticeOn K).Walk x y → ((hypercubicLattice 2).induce K).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro x y hx hy w
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab q ih =>
    
    have hb : b ∈ K := hab.2.2
    have hstep : ((hypercubicLattice 2).induce K).Adj ⟨a, hx⟩ ⟨b, hb⟩ :=
      nbc_induce_adj_of_latticeOn hx hb hab
    exact hstep.reachable.trans (ih hb hy)


theorem nbc_cellConnected_of_isConnectedCluster {K : Finset (Site 2)}
    (h : IsConnectedCluster K) : CellConnected (↑K : Set (Site 2)) := by
  obtain ⟨ho, hreach⟩ := h
  have hoK : origin 2 ∈ (↑K : Set (Site 2)) := by exact_mod_cast ho
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨origin 2, hoK⟩⟩⟩
  intro u v
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  have hru : ((hypercubicLattice 2).induce (↑K : Set (Site 2))).Reachable
      ⟨origin 2, hoK⟩ ⟨u, hu⟩ := by
    obtain ⟨w⟩ := hreach u (by exact_mod_cast hu)
    exact nbc_induce_reachable_of_latticeOn hoK hu w
  have hrv : ((hypercubicLattice 2).induce (↑K : Set (Site 2))).Reachable
      ⟨origin 2, hoK⟩ ⟨v, hv⟩ := by
    obtain ⟨w⟩ := hreach v (by exact_mod_cast hv)
    exact nbc_induce_reachable_of_latticeOn hoK hv w
  exact hru.symm.trans hrv


theorem nbc_isConnectedCluster_of_cellConnected {J : Finset (Site 2)}
    (hoJ : origin 2 ∈ J) (h : CellConnected (↑J : Set (Site 2))) : IsConnectedCluster J := by
  refine ⟨hoJ, ?_⟩
  intro x hx
  have hoJ' : origin 2 ∈ (↑J : Set (Site 2)) := by exact_mod_cast hoJ
  have hxJ' : x ∈ (↑J : Set (Site 2)) := by exact_mod_cast hx
  rw [CellConnected] at h
  have hr := h.preconnected ⟨origin 2, hoJ'⟩ ⟨x, hxJ'⟩
  obtain ⟨p⟩ := hr
  
  exact ⟨p.map (nbc_inclHom (↑J : Set (Site 2)))⟩


theorem nbc_tree_two_leaves {V : Type*} [Fintype V] (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
  classical
  have hNontriv : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  
  have hpos : ∀ v : V, 1 ≤ T.degree v := by
    intro v
    have := hT.connected.preconnected.minDegree_pos_of_nontrivial (G := T)
    exact le_trans this (T.minDegree_le_degree v)
  
  have hsum : ∑ v : V, T.degree v = 2 * #T.edgeFinset := T.sum_degrees_eq_twice_card_edges
  have hedge : #T.edgeFinset + 1 = Fintype.card V := hT.card_edgeFinset
  
  by_contra hcon
  push Not at hcon
  
  
  have hleaf_sub : ∀ a b : V, T.degree a = 1 → T.degree b = 1 → a = b := by
    intro a b ha hb
    by_contra hab
    exact hcon a b hab ha hb
  
  
  obtain ⟨v0, hv0⟩ := hT.exists_vert_degree_one_of_nontrivial
  have hlower : 2 * Fintype.card V - 1 ≤ ∑ v : V, T.degree v := by
    have hbound : ∀ v : V, (if v = v0 then 1 else 2) ≤ T.degree v := by
      intro v
      by_cases hvv : v = v0
      · subst hvv; simp [hv0]
      · simp only [if_neg hvv]
        
        rcases Nat.lt_or_ge (T.degree v) 2 with hlt | hge
        · have h1 : T.degree v = 1 := by have := hpos v; omega
          exact absurd (hleaf_sub v v0 h1 hv0) hvv
        · exact hge
    have hconst : (∑ v : V, (if v = v0 then (1:ℕ) else 2)) + 1 = 2 * Fintype.card V := by
      have hstep : (∑ v : V, (if v = v0 then (1:ℕ) else 2)) + 1
          = ∑ v : V, ((if v = v0 then (1:ℕ) else 2) + (if v = v0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ v0]
        simp only [Finset.mem_univ, if_true]
      rw [hstep]
      have : ∀ v : V, (if v = v0 then (1:ℕ) else 2) + (if v = v0 then 1 else 0) = 2 := by
        intro v; by_cases hvv : v = v0 <;> simp [hvv]
      rw [Finset.sum_congr rfl (fun v _ => this v), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    have hsumif : ∑ v : V, (if v = v0 then (1:ℕ) else 2) ≤ ∑ v : V, T.degree v :=
      Finset.sum_le_sum (fun v _ => hbound v)
    omega
  omega


theorem nbc_induce_mono_left {V : Type*} {T G : SimpleGraph V} (s : Set V) (hle : T ≤ G) :
    T.induce s ≤ G.induce s := by
  intro a b hab
  rw [SimpleGraph.induce_adj] at hab ⊢
  exact hle hab


theorem nbc_cellConnected_diff_of_treeCut {K : Finset (Site 2)}
    {T : SimpleGraph (↑(↑K : Set (Site 2)))}
    (hle : T ≤ (hypercubicLattice 2).induce (↑K : Set (Site 2)))
    {v : ↑(↑K : Set (Site 2))} (h1 : (T.induce ({v}ᶜ : Set _)).Connected) :
    CellConnected ((↑K : Set (Site 2)) \ {v.1}) := by
  classical
  
  have h2 : (((hypercubicLattice 2).induce (↑K : Set (Site 2))).induce
      ({(⟨v.1, v.2⟩ : ↑(↑K : Set (Site 2)))}ᶜ : Set _)).Connected :=
    h1.mono (nbc_induce_mono_left _ hle)
  exact cellConnected_diff_of_iso (↑K : Set (Site 2)) v.1 v.2 h2


theorem nbc_two_noncut {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : CellConnected (↑K : Set (Site 2))) :
    ∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ CellConnected ((↑K : Set (Site 2)) \ {a}) ∧
      CellConnected ((↑K : Set (Site 2)) \ {b}) := by
  classical
  set G := (hypercubicLattice 2).induce (↑K : Set (Site 2)) with hG
  
  have hfin : Fintype (↑(↑K : Set (Site 2))) := FinsetCoe.fintype K
  have hcardV : Fintype.card (↑(↑K : Set (Site 2))) = K.card := by
    simp [Fintype.card_coe]
  
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  haveI : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨a, b, hab, hda, hdb⟩ := nbc_tree_two_leaves T hT (by rw [hcardV]; exact hcard)
  have hca : (T.induce ({a}ᶜ : Set _)).Connected :=
    hT.connected.induce_compl_singleton_of_degree_eq_one hda
  have hcb : (T.induce ({b}ᶜ : Set _)).Connected :=
    hT.connected.induce_compl_singleton_of_degree_eq_one hdb
  refine ⟨a.1, a.2, b.1, b.2, ?_, ?_, ?_⟩
  · intro h; exact hab (Subtype.ext h)
  · exact nbc_cellConnected_diff_of_treeCut hle hca
  · exact nbc_cellConnected_diff_of_treeCut hle hcb


theorem nbc_exists_noncut_ne_origin {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : CellConnected (↑K : Set (Site 2))) :
    ∃ c ∈ K, c ≠ origin 2 ∧ CellConnected ((↑K : Set (Site 2)) \ {c}) := by
  obtain ⟨a, haK, b, hbK, hab, hda, hdb⟩ := nbc_two_noncut hcard hconn
  by_cases ha : a = origin 2
  · refine ⟨b, hbK, ?_, hdb⟩
    intro hb; exact hab (ha.trans hb.symm)
  · exact ⟨a, haK, ha, hda⟩


theorem nbc_coe_erase (K : Finset (Site 2)) (c : Site 2) :
    (↑(K.erase c) : Set (Site 2)) = (↑K : Set (Site 2)) \ {c} := by
  ext x
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]


theorem nbc_isConnectedCluster_erase {K : Finset (Site 2)} {c : Site 2}
    (ho : origin 2 ∈ K) (hcorigin : c ≠ origin 2)
    (h : CellConnected ((↑K : Set (Site 2)) \ {c})) : IsConnectedCluster (K.erase c) := by
  have hoerase : origin 2 ∈ K.erase c := Finset.mem_erase.mpr ⟨fun h => hcorigin h.symm, ho⟩
  apply nbc_isConnectedCluster_of_cellConnected hoerase
  rw [CellConnected, nbc_coe_erase]
  rw [CellConnected] at h; exact h


end Walls
end StatMech
