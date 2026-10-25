/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCycleSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
open SimpleGraph Set List Function


namespace StatMech

namespace Lattice

theorem jcs_support_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) : c.support.toFinset.card = c.length := by
  have h3 := hc.three_le_length
  have hslen : c.support.length = c.length + 1 := Walk.length_support c
  have hsupp : c.support = v :: c.support.tail := (Walk.cons_tail_support c).symm
  have htlen : c.support.tail.length = c.length := by
    have h' : (v :: c.support.tail).length = c.length + 1 := hsupp ▸ hslen
    simp only [List.length_cons] at h'; omega
  have hvtail : v ∈ c.support.tail := by
    have hgl : c.support.getLast? = some v := by
      rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil c), c.getLast_support]
    have : c.support.tail.getLast? = some v := by
      rw [List.getLast?_tail, if_neg (by omega), hgl]
    exact List.mem_of_getLast? this
  rw [hsupp, List.toFinset_cons, Finset.insert_eq_self.mpr (by simp [hvtail]),
    List.toFinset_card_of_nodup hc.support_nodup, htlen]


theorem jcs_coe_mem {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (e : Sym2 H.verts)
    (he : e ∈ H.coe.edgeSet) : Sym2.map Subtype.val e ∈ H.edgeSet := by
  rw [Subgraph.edgeSet_coe] at he; exact he


theorem jcs_coe_mem' {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) (e : Sym2 H.verts)
    (he : Sym2.map Subtype.val e ∈ H.edgeSet) : e ∈ H.coe.edgeSet := by
  rw [Subgraph.edgeSet_coe]; exact he


theorem jcs_coe_edge_card {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) :
    Nat.card H.coe.edgeSet = Nat.card H.edgeSet := by
  apply Nat.card_eq_of_bijective (fun e => ⟨Sym2.map Subtype.val e.1, jcs_coe_mem H e.1 e.2⟩)
  refine ⟨?_, ?_⟩
  · rintro ⟨e, he⟩ ⟨e', he'⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact Sym2.map.injective Subtype.val_injective h
  · rintro ⟨e, he⟩
    induction e with
    | h a b =>
      have ha : a ∈ H.verts := H.mem_verts_of_mem_edge he (by simp)
      have hb : b ∈ H.verts := H.mem_verts_of_mem_edge he (by simp)
      exact ⟨⟨s(⟨a, ha⟩, ⟨b, hb⟩), jcs_coe_mem' H _ (by simpa using he)⟩,
        by simp only [Subtype.mk.injEq]; rfl⟩


theorem jcs_walk_edgeSet_ncard {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) : c.edgeSet.ncard = c.length := by
  classical
  have : c.edgeSet = (↑c.edges.toFinset : Set (Sym2 V)) := by ext e; simp [Walk.edgeSet]
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hc.edges_nodup, Walk.length_edges]


end Lattice
end StatMech
