/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Instance.StatisticalMechanics.Code.FK.SuperMultiplicative
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Edges

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_edgeSet_sum :
    (G ⊕g H).edgeSet =
      (Sym2.map Sum.inl '' G.edgeSet) ∪ (Sym2.map Sum.inr '' H.edgeSet) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeSet, Set.mem_union, Set.mem_image]
    match x, y with
    | Sum.inl a, Sum.inl b =>
      constructor
      · intro h
        exact Or.inl ⟨s(a,b), by simpa [mem_edgeSet] using h, by simp⟩
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩)
        · induction z using Sym2.ind with
          | _ c d =>
            simp only [Sym2.map_mk] at hmap
            rw [mem_edgeSet] at hz
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hc, hd⟩ | ⟨hc, hd⟩
            · cases hc; cases hd; simpa [mem_edgeSet] using hz
            · cases hc; cases hd; simpa [SimpleGraph.sum_adj] using hz.symm
        · exfalso
          induction z using Sym2.ind with
          | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto
    | Sum.inr a, Sum.inr b =>
      constructor
      · intro h
        exact Or.inr ⟨s(a,b), by simpa [mem_edgeSet] using h, by simp⟩
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩)
        · exfalso
          induction z using Sym2.ind with
          | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto
        · induction z using Sym2.ind with
          | _ c d =>
            simp only [Sym2.map_mk] at hmap
            rw [mem_edgeSet] at hz
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hc, hd⟩ | ⟨hc, hd⟩
            · cases hc; cases hd; simpa [mem_edgeSet] using hz
            · cases hc; cases hd; simpa [SimpleGraph.sum_adj] using hz.symm
    | Sum.inl a, Sum.inr b =>
      simp only [SimpleGraph.sum_adj]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩) <;>
          (induction z using Sym2.ind with
           | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto)
    | Sum.inr a, Sum.inl b =>
      simp only [SimpleGraph.sum_adj]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩) <;>
          (induction z using Sym2.ind with
           | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto)


theorem fsm_edgeFinset_sum :
    (G ⊕g H).edgeFinset =
      (G.edgeFinset.image (Sym2.map Sum.inl)) ∪ (H.edgeFinset.image (Sym2.map Sum.inr)) := by
  ext e
  simp only [mem_edgeFinset, Finset.mem_union, Finset.mem_image, mem_edgeFinset]
  have he : e ∈ (G ⊕g H).edgeSet ↔
      (∃ z ∈ G.edgeSet, Sym2.map Sum.inl z = e) ∨ (∃ z ∈ H.edgeSet, Sym2.map Sum.inr z = e) := by
    rw [fsm_edgeSet_sum]; simp [Set.mem_image]
  rw [he]

theorem fsm_map_inl_injective : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ W)) :=
  Sym2.map.injective Sum.inl_injective

theorem fsm_map_inr_injective : Function.Injective (Sym2.map (Sum.inr : W → V ⊕ W)) :=
  Sym2.map.injective Sum.inr_injective


theorem fsm_images_disjoint :
    Disjoint (G.edgeFinset.image (Sym2.map (Sum.inl : V → V ⊕ W)))
             (H.edgeFinset.image (Sym2.map (Sum.inr : W → V ⊕ W))) := by
  rw [Finset.disjoint_left]
  rintro e he1 he2
  rw [Finset.mem_image] at he1 he2
  obtain ⟨z1, _, rfl⟩ := he1
  obtain ⟨z2, _, hz2⟩ := he2
  induction z1 using Sym2.ind with
  | _ a b =>
    induction z2 using Sym2.ind with
    | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hz2; tauto

end Edges
end FK
end StatMech
