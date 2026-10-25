/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem walk_induce_reachable {V : Type*} (G : SimpleGraph V) (s : Set V)
    {x y : V} (w : G.Walk x y) (hw : ∀ z ∈ w.support, z ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) : (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have hb : b ∈ s := hw b (by simp)
    exact ((show (G.induce s).Adj ⟨a, hx⟩ ⟨b, hb⟩ from hab).reachable).trans
      (ih (fun z hz => hw z (by simp [hz])) hb hy)


theorem latticeMinusBarrier_adj_of_both_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∈ S) (hy : y ∈ S) :
    (latticeMinusBarrier S).Adj x y :=
  ⟨hadj, by rw [bdEdge_mk]; tauto⟩


theorem latticeMinusBarrier_adj_of_both_not_mem (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hx : x ∉ S) (hy : y ∉ S) :
    (latticeMinusBarrier S).Adj x y :=
  ⟨hadj, by rw [bdEdge_mk]; tauto⟩


theorem openWalk_support_mem_cluster (o : Site 2) {y : Site 2}
    (w : (openSubgraph 2 ω).Walk o y) : ∀ z ∈ w.support, z ∈ cluster 2 ω o :=
  fun z hz => (w.takeUntil z hz).reachable


end Lattice
end StatMech
