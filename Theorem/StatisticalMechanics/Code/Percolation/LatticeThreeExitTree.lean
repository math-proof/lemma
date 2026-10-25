/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Def.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree.Part2
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d n : ℕ}


theorem threeExitTip_injective :
    Function.Injective (threeExitTip (d := d) (n := n)) := Sum.inr_injective


theorem threeExitTip_degree_one (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) (i : Fin 3) :
    (threeExitGraph (n := n) inside).degree (threeExitTip i) = 1 := by
  classical
  rw [degree_eq_one_iff_existsUnique_adj]
  let q : ↑(boxFinsetBK d n) := ⟨inside i, by simpa [boxFinsetBK] using hinside i⟩
  refine ⟨Sum.inl q, by simp [threeExitGraph, threeExitTip, q], ?_⟩
  intro z hz
  rcases z with z | j
  · simp only [threeExitGraph] at hz
    exact congrArg Sum.inl (Subtype.ext hz)
  · simp [threeExitGraph, threeExitTip] at hz

theorem boxEdgeWalk_support_mem {x y : Site d}
    (w : (openSubgraph d (forceOpenFinset (boxEdges d n) (fun _ => false))).Walk x y)
    (hx : x ∈ box d n) : ∀ z ∈ w.support, z ∈ box d n := by
  induction w with
  | nil =>
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hx
  | @cons a b c hab w ih =>
      intro z hz
      simp only [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx
      · have hedge : s(a, b) ∈ boxEdges d n := by
          rw [openSubgraph_adj] at hab
          rcases hab with ⟨_, hopen⟩
          simpa [forceOpenFinset] using hopen
        have hb : b ∈ box d n := (mem_boxEdges_iff.mp hedge).2.1
        exact ih hb z hz


theorem threeExitGraph_core_reachable (inside : Fin 3 → Site d)
    {x y : ↑(boxFinsetBK d n)} :
    (threeExitGraph inside).Reachable (Sum.inl x) (Sum.inl y) := by
  classical
  have hx : x.1 ∈ box d n := by
    simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using x.2
  have hy : y.1 ∈ box d n := by
    simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using y.2
  obtain ⟨w⟩ := box_allOpen_reachable (fun _ => false) hx hy
  have hwbox : ∀ z ∈ w.support, z ∈ box d n :=
    boxEdgeWalk_support_mem w hx
  let wi := w.induce (box d n) hwbox
  let f : (openSubgraph d
      (forceOpenFinset (boxEdges d n) (fun _ => false))).induce (box d n) →g
      threeExitGraph inside := {
    toFun := fun z => Sum.inl ⟨z.1, by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using z.2⟩
    map_rel' := by
      intro a b hab
      exact (openSubgraph_le _ hab)
  }
  exact ⟨wi.map f⟩


theorem threeExitGraph_connected (inside : Fin 3 → Site d)
    (hinside : ∀ i, inside i ∈ box d n) :
    (threeExitGraph (n := n) inside).Connected := by
  classical
  rw [connected_iff]
  refine ⟨?_, ⟨Sum.inr 0⟩⟩
  intro a b
  let core : Fin 3 → ↑(boxFinsetBK d n) := fun i =>
    ⟨inside i, by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using hinside i⟩
  have tip_core : ∀ i, (threeExitGraph inside).Adj (Sum.inr i) (Sum.inl (core i)) := by
    intro i
    simp [threeExitGraph, core]
  have toCore : ∀ z : ThreeExitVertex d n,
      ∃ q : ↑(boxFinsetBK d n), (threeExitGraph inside).Reachable z (Sum.inl q) := by
    rintro (q | i)
    · exact ⟨q, Reachable.refl _⟩
    · exact ⟨core i, (tip_core i).reachable⟩
  obtain ⟨qa, ha⟩ := toCore a
  obtain ⟨qb, hb⟩ := toCore b
  exact ha.trans ((threeExitGraph_core_reachable inside).trans hb.symm)


end StatMech.Percolation
