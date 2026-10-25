/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part7
import Def.StatisticalMechanics.Code.Walls.binsclosure
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000


theorem bins_walk_edge_mem_touch {n : ℕ} {x y : Site 2}
    (P : (hypercubicLattice 2).Walk x y)
    (hbox : ∀ z ∈ P.support, z ∈ box 2 n) :
    P.edges.toFinset ⊆ bondFinsetTouch 2 n := by
  intro e he
  rw [List.mem_toFinset] at he
  induction P with
  | nil => simp at he
  | @cons x y z hxy P ih =>
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rw [hbx_mem_bondFinsetTouch_iff]
        exact ⟨hxy, Or.inl (hbox x (by simp))⟩
      · apply ih
        intro w hw
        exact hbox w (by simp [hw])
        exact he


theorem bins_extCluster_avoids_box (n : ℕ) (omega : ConfigSpace (Sym2 (Site 2)))
    (u : Site 2) (hu : u ∉ box 2 n) :
    Disjoint (cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) u)
      (box 2 n) := by
  rw [Set.disjoint_left]
  intro z hz hzbox
  rw [bins_cluster_closeTouch_eq_removeBox] at hz
  have hconn : Connected 2 (removeSites (boxFinset 2 n) omega) u z := mem_cluster.mp hz
  have humem : u ∈ cluster 2 (removeSites (boxFinset 2 n) omega) z :=
    mem_cluster.mpr hconn.symm
  have hzfin : z ∈ boxFinset 2 n := by
    rw [mem_boxFinset]
    exact hzbox
  rw [stac_removeSites_cluster_singleton (boxFinset 2 n) omega hzfin] at humem
  have huz : u = z := by simpa using humem
  exact hu (huz ▸ hzbox)


end StatMech.Walls
