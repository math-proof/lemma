/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Def.StatisticalMechanics.Code.Walls.bc18mengerhard


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}


omit [DecidableEq V] in
theorem bc18_subset_AReach (G : SimpleGraph V) (A S : Set V) : A ⊆ bc18_AReach G A S := by
  intro a ha
  exact ⟨a, ha, Walk.nil, fun z hz _ => by
    rw [Walk.support_nil, List.mem_singleton] at hz; exact hz⟩


theorem bc18_mem_AReach_of_mem_support {A S : Set V} {a v : V}
    (ha : a ∈ A) {q : G.Walk a v} (hqpath : q.IsPath)
    (hq : ∀ z ∈ q.support, z ∈ S → z = v) {z : V} (hz : z ∈ q.support) :
    z ∈ bc18_AReach G A S := by
  refine ⟨a, ha, q.takeUntil z hz, ?_⟩
  intro w hw hwS
  have hwq : w ∈ q.support := q.support_takeUntil_subset_support hz hw
  have hwv : w = v := hq w hwq hwS
  by_cases hzv : z = v
  · subst hzv; exact hwv
  · subst hwv
    exact absurd hw (Walk.endpoint_notMem_support_takeUntil hqpath hz (Ne.symm hzv))


theorem bc18_AReach_separator_transfer {A B S C : Set V}
    (hS : bc16_IsSeparator G A B S)
    (hC : bc16_IsSeparator (bc17_restr G (bc18_AReach G A S)) A S C) :
    bc16_IsSeparator G A B C := by
  intro s hs t ht p
  obtain ⟨w, hwS, hwp⟩ := hS hs ht p
  obtain ⟨c, q, hqpath, hcS, hqsub, hq⟩ := bc18_firstHitPath p ⟨w, hwp, hwS⟩
  have hedges : ∀ e ∈ q.edges, e ∈ (bc17_restr G (bc18_AReach G A S)).edgeSet := by
    intro e he
    obtain ⟨w₁, w₂⟩ := e
    rw [mem_edgeSet, bc17_restr_adj]
    exact ⟨q.adj_of_mem_edges he,
      bc18_mem_AReach_of_mem_support hs hqpath hq (q.fst_mem_support_of_mem_edges he),
      bc18_mem_AReach_of_mem_support hs hqpath hq (q.snd_mem_support_of_mem_edges he)⟩
  obtain ⟨c', hc'C, hc'q⟩ := hC hs hcS (q.transfer _ hedges)
  refine ⟨c', hc'C, ?_⟩
  rw [Walk.support_transfer] at hc'q
  exact hqsub hc'q


omit [DecidableEq V] in


theorem bc18_splitAtEdge {K : SimpleGraph V} {x y a₀ b₀ : V} (R : K.Walk a₀ b₀) :
    (K.deleteEdges {s(x, y)}).Reachable a₀ b₀ ∨
    ((K.deleteEdges {s(x, y)}).Reachable a₀ x ∧ (K.deleteEdges {s(x, y)}).Reachable y b₀) ∨
    ((K.deleteEdges {s(x, y)}).Reachable a₀ y ∧ (K.deleteEdges {s(x, y)}).Reachable x b₀) := by
  classical
  induction R with
  | nil => exact Or.inl (Reachable.refl _)
  | cons hadj t ih =>
      rename_i u v w
      by_cases hcase : s(u, v) = s(x, y)
      · rw [Sym2.eq_iff] at hcase
        rcases hcase with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst hu; subst hv
          rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
          · exact Or.inr (Or.inl ⟨Reachable.refl _, h⟩)
          · exact Or.inr (Or.inl ⟨Reachable.refl _, h2⟩)
          · exact Or.inl h2
        · subst hu; subst hv
          rcases ih with h | ⟨_, h2⟩ | ⟨_, h2⟩
          · exact Or.inr (Or.inr ⟨Reachable.refl _, h⟩)
          · exact Or.inl h2
          · exact Or.inr (Or.inr ⟨Reachable.refl _, h2⟩)
      · have hKe : (K.deleteEdges {s(x, y)}).Adj u v := by
          rw [deleteEdges_adj]
          exact ⟨hadj, by simp only [Set.mem_singleton_iff]; exact hcase⟩
        have hstep : (K.deleteEdges {s(x, y)}).Reachable u v := ⟨Walk.cons hKe Walk.nil⟩
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (hstep.trans h)
        · exact Or.inr (Or.inl ⟨hstep.trans h1, h2⟩)
        · exact Or.inr (Or.inr ⟨hstep.trans h1, h2⟩)


end StatMech.Walls
