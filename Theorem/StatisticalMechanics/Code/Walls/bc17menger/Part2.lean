/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Def.StatisticalMechanics.Code.Walls.bc17menger.Part2


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


omit [DecidableEq V] in


theorem bc17_hard_bot [Fintype V] (A B : Set V) {k : ℕ}
    (hsep : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k)) := by
  have hk : k ≤ (A ∩ B).ncard := hsep _ (bc17_inter_isSeparator_bot A B)
  obtain ⟨f, hinj, hf⟩ := bc17_exists_finInj_of_le_ncard (Set.toFinite (A ∩ B)) hk
  exact ⟨bc17_botFamily hinj hf⟩


variable {G : SimpleGraph V}

omit [DecidableEq V] in

theorem bc17_edgeSet_ncard_lt_of_deleteEdge [Fintype V] {x y : V} (h : G.Adj x y) :
    (G.deleteEdges {s(x, y)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  refine Set.ncard_lt_ncard ⟨Set.diff_subset, ?_⟩ (Set.toFinite _)
  intro hsub
  have hmem : s(x, y) ∈ G.edgeSet := by simpa using h
  simpa using hsub hmem


theorem bc17_insert_isSeparator_left {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B (insert x Y) := by
  intro s hs t ht p
  by_cases he : s(x, y) ∈ p.edges
  · exact ⟨x, Set.mem_insert _ _, p.fst_mem_support_of_mem_edges he⟩
  · obtain ⟨c, hcY, hcp⟩ := hY hs ht (p.toDeleteEdge (s(x, y)) he)
    exact ⟨c, Set.mem_insert_of_mem _ hcY, by rwa [Walk.support_transfer] at hcp⟩


theorem bc17_insert_isSeparator_right {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y) :
    bc16_IsSeparator G A B (insert y Y) := by
  intro s hs t ht p
  by_cases he : s(x, y) ∈ p.edges
  · refine ⟨y, Set.mem_insert _ _, ?_⟩
    exact p.snd_mem_support_of_mem_edges he
  · obtain ⟨c, hcY, hcp⟩ := hY hs ht (p.toDeleteEdge (s(x, y)) he)
    exact ⟨c, Set.mem_insert_of_mem _ hcY, by rwa [Walk.support_transfer] at hcp⟩


theorem bc17_endpoints_notMem_of_not_isSeparator {A B Y : Set V} {x y : V}
    (hY : bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y)
    (hnotG : ¬ bc16_IsSeparator G A B Y) : x ∉ Y ∧ y ∉ Y := by
  refine ⟨fun hx => hnotG ?_, fun hy => hnotG ?_⟩
  · rw [← Set.insert_eq_self.mpr hx]; exact bc17_insert_isSeparator_left hY
  · rw [← Set.insert_eq_self.mpr hy]; exact bc17_insert_isSeparator_right hY


theorem bc17_deleteEdge_dichotomy [Fintype V] {A B : Set V} {x y : V}
    (hxy : G.Adj x y) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) :
    (∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) ∨
    (∃ Y : Set V, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B Y ∧ Y.ncard < k ∧
      x ∉ Y ∧ y ∉ Y ∧ bc16_IsSeparator G A B (insert x Y) ∧
      bc16_IsSeparator G A B (insert y Y)) := by
  classical
  by_cases hcase : ∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard
  · exact Or.inl hcase
  · refine Or.inr ?_
    push Not at hcase
    obtain ⟨Y, hY, hYlt⟩ := hcase
    
    have hnotG : ¬ bc16_IsSeparator G A B Y := fun hG => absurd (hmin Y hG) (by omega)
    obtain ⟨hx, hy⟩ := bc17_endpoints_notMem_of_not_isSeparator hY hnotG
    exact ⟨Y, hY, hYlt, hx, hy, bc17_insert_isSeparator_left hY,
      bc17_insert_isSeparator_right hY⟩


omit [DecidableEq V] in

theorem bc17_hard_zero (G : SimpleGraph V) (A B : Set V) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin 0)) :=
  ⟨{ a := fun i => i.elim0, b := fun i => i.elim0, p := fun i => i.elim0,
     ha := fun i => i.elim0, hb := fun i => i.elim0, hp := fun i => i.elim0,
     hdisj := fun i => i.elim0 }⟩

omit [DecidableEq V] in


theorem bc17_hard_one (G : SimpleGraph V) (A B : Set V)
    (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin 1)) := by
  
  have hne : ¬ bc16_IsSeparator G A B (∅ : Set V) := by
    intro h
    have := hmin _ h
    simp at this
  obtain ⟨s, hs, t, ht, p, hp⟩ := bc16_exists_path_of_not_empty_separator hne
  exact ⟨{ a := fun _ => s, b := fun _ => t, p := fun _ => p,
           ha := fun _ => hs, hb := fun _ => ht, hp := fun _ => hp,
           hdisj := fun i j hij => absurd (Subsingleton.elim i j) hij }⟩


end StatMech.Walls
