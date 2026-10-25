/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CriticalFreeShellSummability
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part2
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

noncomputable section

@[simp] theorem squareRegionConfig_mk_eq_true
    (K : Set (Site 2)) (x y : Site 2) :
    squareRegionConfig K s(x, y) = true ↔ x ∈ K ∧ y ∈ K := by
  classical
  simp [squareRegionConfig]

theorem squareRegionConfig_cluster_eq
    (K : Set (Site 2)) (hzero : origin 2 ∈ K)
    (hconn : ∀ a b : K,
      ((hypercubicLattice 2).induce K).Reachable a b) :
    cluster 2 (squareRegionConfig K) (origin 2) = K := by
  ext y
  rw [mem_cluster]
  constructor
  · intro hy
    obtain ⟨w⟩ := hy
    have walk_end_mem : ∀ {a b : Site 2}
        (p : (openSubgraph 2 (squareRegionConfig K)).Walk a b),
        a ∈ K → b ∈ K := by
      intro a b p ha
      induction p with
      | nil => exact ha
      | @cons a b c hab p ih =>
          have hb : b ∈ K := by
            rw [openSubgraph_adj] at hab
            exact (squareRegionConfig_mk_eq_true K a b).1 hab.2 |>.2
          exact ih hb
    exact walk_end_mem w hzero
  · intro hy
    obtain ⟨w⟩ := hconn ⟨origin 2, hzero⟩ ⟨y, hy⟩
    let incl : (hypercubicLattice 2).induce K →g
        openSubgraph 2 (squareRegionConfig K) :=
      { toFun := Subtype.val
        map_rel' := fun {a b} hab => by
          refine ⟨hab, ?_⟩
          exact (squareRegionConfig_mk_eq_true K a b).2 ⟨a.2, b.2⟩ }
    simpa [incl] using Reachable.map incl ⟨w⟩


theorem latticeWalk_hits_l1Sphere
    (center : Site 2) {a b : Site 2}
    (w : (hypercubicLattice 2).Walk a b) (n : Nat)
    (ha : l1dist 2 center a ≤ n) (hb : n ≤ l1dist 2 center b) :
    ∃ z ∈ w.support, l1dist 2 center z = n := by
  induction w with
  | nil =>
      refine ⟨_, by simp, Nat.le_antisymm ha hb⟩
  | @cons a c b hac w ih =>
      by_cases heq : l1dist 2 center a = n
      · exact ⟨a, by simp, heq⟩
      · have hac_le : l1dist 2 center c ≤ n := by
          have htri := l1dist_triangle 2 center a c
          rw [l1dist_of_adj 2 hac] at htri
          omega
        obtain ⟨z, hz, hdist⟩ := ih hac_le hb
        exact ⟨z, by simp [hz], hdist⟩


end
end StatMech.FrontierD
