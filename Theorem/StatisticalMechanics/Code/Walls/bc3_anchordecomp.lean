/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_anchordecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.bc3_anchordecomp
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


@[simp] lemma bc3_mem_anchorSites {G : Finset (Sym2 (Site d))} {a : Site d} :
    a ∈ bc3_anchorSites G ↔ ∃ e ∈ G, a ∈ e := Iff.rfl


theorem bc3_anchorSites_finite (G : Finset (Sym2 (Site d))) : (bc3_anchorSites G).Finite := by
  have hsub : bc3_anchorSites G ⊆ ⋃ e ∈ G, {a | a ∈ e} := by
    intro a ha; obtain ⟨e, he, hae⟩ := ha; exact Set.mem_biUnion he hae
  refine Set.Finite.subset (Set.Finite.biUnion G.finite_toSet ?_) hsub
  intro e _
  induction e with
  | h p q =>
    refine Set.Finite.subset ((Set.finite_singleton q).insert p) ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Sym2.mem_iff] at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact ha


theorem bc3_anchor_decomp (G : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (x z : Site d) (h : Connected d (forceOpenFinset G ω) x z) :
    Connected d ω x z ∨ ∃ a ∈ bc3_anchorSites G, Connected d ω a z := by
  unfold Connected at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl connected_rfl
  | @tail b c hxb hbc ih =>
    rcases adj_forceOpenFinset_cases G ω hbc with hadj | hF
    · 
      rcases ih with hxb' | ⟨a, ha, hab⟩
      · exact Or.inl (hxb'.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj))
      · exact Or.inr ⟨a, ha, hab.trans (SimpleGraph.Adj.reachable (G := openSubgraph d ω) hadj)⟩
    · 
      exact Or.inr ⟨c, ⟨s(b, c), hF, Sym2.mem_mk_right b c⟩, connected_rfl⟩


theorem bc3_cluster_covered_by_anchors (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    cluster d (forceOpenFinset G ω) x ⊆
      ⋃ a ∈ insert x (bc3_anchorSites G), cluster d ω a := by
  intro z hz
  rw [mem_cluster] at hz
  rcases bc3_anchor_decomp G ω x z hz with hconn | ⟨a, ha, haz⟩
  · exact Set.mem_biUnion (Set.mem_insert x _) (by rw [mem_cluster]; exact hconn)
  · exact Set.mem_biUnion (Set.mem_insert_of_mem x ha) (by rw [mem_cluster]; exact haz)


theorem bc3_anchor_cover_index_finite (G : Finset (Sym2 (Site d))) (x : Site d) :
    (insert x (bc3_anchorSites G)).Finite := (bc3_anchorSites_finite G).insert x


end Walls
end StatMech
