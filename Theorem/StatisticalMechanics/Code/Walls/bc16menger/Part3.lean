/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Def.StatisticalMechanics.Code.Walls.bc16menger.Part2


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


theorem bc16_hitVertex_mem_separator {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    bc16_hitVertex F hC i ∈ C :=
  (bc16_separator_hits_path F hC i).choose_spec.1

theorem bc16_hitVertex_mem_support {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    bc16_hitVertex F hC i ∈ (F.p i).support :=
  (bc16_separator_hits_path F hC i).choose_spec.2


theorem bc16_hitVertex_injective {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) :
    Function.Injective (bc16_hitVertex F hC) := by
  intro i j hij
  by_contra hne
  
  have hi : bc16_hitVertex F hC i ∈ (F.p i).support := bc16_hitVertex_mem_support F hC i
  have hj : bc16_hitVertex F hC j ∈ (F.p j).support := bc16_hitVertex_mem_support F hC j
  rw [hij] at hi
  exact F.hdisj hne hi hj


theorem bc16_max_le_min {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C)
    (hCfin : C.Finite) :
    (Set.univ : Set ι).ncard ≤ C.ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (bc16_hitVertex F hC) ?_ ?_ hCfin
  · intro i _
    exact bc16_hitVertex_mem_separator F hC i
  · intro i _ j _ hij
    exact bc16_hitVertex_injective F hC hij


theorem bc16_card_le_ncard_separator {S T C : Set V} {ι : Type*} [Finite V]
    [Fintype ι] (F : bc16_DisjointPathFamily G S T ι)
    (hC : bc16_IsSeparator G S T C) :
    Fintype.card ι ≤ C.ncard := by
  have hCfin : C.Finite := Set.toFinite C
  have h := bc16_max_le_min F hC hCfin
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h


theorem bc16_encard_le_encard_separator {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) :
    (Set.univ : Set ι).encard ≤ C.encard := by
  classical
  have hmaps : Set.MapsTo (bc16_hitVertex F hC) (Set.univ : Set ι) C := by
    intro i _
    exact bc16_hitVertex_mem_separator F hC i
  have hinj : Set.InjOn (bc16_hitVertex F hC) (Set.univ : Set ι) := by
    intro i _ j _ hij
    exact bc16_hitVertex_injective F hC hij
  exact Set.encard_le_encard_of_injOn hmaps hinj


theorem bc16_source_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T S := by
  intro s hs t _ p
  exact ⟨s, hs, p.start_mem_support⟩


theorem bc16_target_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T T := by
  intro s _ t ht p
  exact ⟨t, ht, p.end_mem_support⟩


theorem bc16_no_walk_of_empty_separator {S T : Set V}
    (h : bc16_IsSeparator G S T (∅ : Set V)) {s t : V} (hs : s ∈ S) (ht : t ∈ T)
    (p : G.Walk s t) : False := by
  obtain ⟨c, hc, _⟩ := h hs ht p
  exact (Set.notMem_empty c) hc


theorem bc16_empty_separator_of_no_walk {S T : Set V}
    (h : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → IsEmpty (G.Walk s t)) :
    bc16_IsSeparator G S T (∅ : Set V) := by
  intro s hs t ht p
  exact (h hs ht).false p |>.elim


theorem bc16_empty_separator_iff_not_reachable {S T : Set V} :
    bc16_IsSeparator G S T (∅ : Set V) ↔
      ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → ¬ G.Reachable s t := by
  constructor
  · intro h s hs t ht hr
    obtain ⟨p⟩ := hr
    exact bc16_no_walk_of_empty_separator h hs ht p
  · intro h s hs t ht p
    exact absurd p.reachable (h hs ht)


theorem bc16_exists_path_of_not_empty_separator {S T : Set V}
    (h : ¬ bc16_IsSeparator G S T (∅ : Set V)) :
    ∃ (s : V) (_ : s ∈ S) (t : V) (_ : t ∈ T) (p : G.Walk s t), p.IsPath := by
  
  rw [bc16_IsSeparator] at h
  push Not at h
  obtain ⟨s, hs, t, ht, p, _⟩ := h
  obtain ⟨q, hq⟩ := p.reachable.exists_isPath
  exact ⟨s, hs, t, ht, q, hq⟩


end StatMech.Walls
