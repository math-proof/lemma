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
import Def.StatisticalMechanics.Code.Walls.bc17menger.Part4


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


variable {G : SimpleGraph V}

@[simp] theorem bc17_restr_adj (G : SimpleGraph V) (W : Set V) {u v : V} :
    (bc17_restr G W).Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W := Iff.rfl

omit [DecidableEq V] in

theorem bc17_restr_le (G : SimpleGraph V) (W : Set V) : bc17_restr G W ≤ G :=
  fun _ _ h => h.1

omit [DecidableEq V] in

theorem bc17_restr_support_subset (G : SimpleGraph V) (W : Set V) {a b : V} (ha : a ∈ W)
    (p : (bc17_restr G W).Walk a b) : ∀ z ∈ p.support, z ∈ W := by
  induction p with
  | nil => intro z hz; rw [Walk.support_nil, List.mem_singleton] at hz; exact hz ▸ ha
  | @cons u v w h q ih =>
      intro z hz
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ha
      · exact ih h.2.2 z hz

omit [DecidableEq V] in

theorem bc17_restr_edgeSet_subset (G : SimpleGraph V) (W : Set V) :
    (bc17_restr G W).edgeSet ⊆ G.edgeSet := edgeSet_mono (bc17_restr_le G W)


theorem bc17_restr_edgeSet_ncard_lt [Fintype V] (G : SimpleGraph V) (W : Set V) {x y : V}
    (hxy : G.Adj x y) (hy : y ∉ W) :
    (bc17_restr G W).edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ⟨bc17_restr_edgeSet_subset G W, ?_⟩ (Set.toFinite _)
  intro hsub
  have hmem : s(x, y) ∈ G.edgeSet := by simpa using hxy
  have := hsub hmem
  rw [mem_edgeSet, bc17_restr_adj] at this
  exact hy this.2.2


omit [DecidableEq V] in


theorem bc17_minmax_one [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (hmin : ∀ C, bc16_IsSeparator G A B C → 1 ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily G A B (Fin 1),
      ∀ C, bc16_IsSeparator G A B C → Fintype.card (Fin 1) ≤ C.ncard := by
  obtain ⟨F⟩ := bc17_hard_one G A B hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩


theorem bc17_minmax_bot [Fintype V] (A B : Set V) {k : ℕ}
    (hmin : ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → k ≤ C.ncard) :
    ∃ F : bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k),
      ∀ C, bc16_IsSeparator (⊥ : SimpleGraph V) A B C → Fintype.card (Fin k) ≤ C.ncard := by
  obtain ⟨F⟩ := bc17_hard_bot A B hmin
  exact ⟨F, fun C hC => by simpa using hmin C hC⟩

end StatMech.Walls
