/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.FaceRegion.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem cutLattice_adj (S : Set (Site 2)) (x y : Site 2) :
    (cutLattice S).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ s(x, y) ∉ bdEdgeSet2 S := by
  rw [cutLattice, deleteEdges_adj]


theorem cutLattice_le (S : Set (Site 2)) : cutLattice S ≤ hypercubicLattice 2 := by
  rw [cutLattice]; exact deleteEdges_le _


theorem cutLattice_adj_of_both_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∈ S) (hy : y ∈ S) :
    (cutLattice S).Adj x y := by
  rw [cutLattice_adj]
  refine ⟨hadj, ?_⟩
  rw [mem_bdEdgeSet2]
  tauto


theorem cutLattice_adj_preserves (S : Set (Site 2)) {x y : Site 2}
    (hadj : (cutLattice S).Adj x y) (hx : x ∈ S) : y ∈ S := by
  rw [cutLattice_adj] at hadj
  obtain ⟨_, hne⟩ := hadj
  by_contra hy
  exact hne ((mem_bdEdgeSet2 S x y).mpr ⟨fun _ => hy, fun _ => hx⟩)


theorem cutLattice_walk_preserves (S : Set (Site 2)) {x y : Site 2}
    (w : (cutLattice S).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (cutLattice_adj_preserves S hab hx)


theorem cutLattice_reachable_preserves (S : Set (Site 2)) {x y : Site 2}
    (h : (cutLattice S).Reachable x y) (hx : x ∈ S) : y ∈ S := by
  obtain ⟨w⟩ := h
  exact cutLattice_walk_preserves S w hx


theorem cutLattice_not_reachable (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) : ¬ (cutLattice S).Reachable x y := by
  intro h
  exact hy (cutLattice_reachable_preserves S h hx)


variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem openWalk_to_cutLattice (o : Site 2) {x y : Site 2}
    (w : (openSubgraph 2 ω).Walk x y) (hx : x ∈ cluster 2 ω o) :
    (cutLattice (cluster 2 ω o)).Reachable x y := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hab _ ih =>
    have hb : b ∈ cluster 2 ω o := hx.trans (IsOpenEdge.connected hab)
    exact ((cutLattice_adj_of_both_mem _ hab.1 hx hb).reachable).trans (ih hb)


theorem cutLattice_reachable_of_connected (o : Site 2) {x : Site 2}
    (hx : x ∈ cluster 2 ω o) : (cutLattice (cluster 2 ω o)).Reachable o x := by
  obtain ⟨w⟩ := (hx : (openSubgraph 2 ω).Reachable o x)
  exact openWalk_to_cutLattice o w (self_mem_cluster ω o)


end Lattice
end StatMech
