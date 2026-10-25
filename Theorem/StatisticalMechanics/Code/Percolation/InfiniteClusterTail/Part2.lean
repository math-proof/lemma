/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Percolation.InfiniteClusterTail.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

theorem tailComponentSites_infinite
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K))
    (hD : D.supp.Infinite) : (tailComponentSites omega x K D).Infinite := by
  exact hD.image Subtype.val_injective.injOn

theorem tailComponentSites_subset_cluster
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    tailComponentSites omega x K D ⊆ cluster d omega x := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem tailComponentSites_connected_outside
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d) (K : Finset (Site d))
    (D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)) :
    ∀ u ∈ tailComponentSites omega x K D,
      ∀ v ∈ tailComponentSites omega x K D,
        ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩ := by
  rintro u ⟨uC, huD, rfl⟩ v ⟨vC, hvD, rfl⟩
  rcases huD with ⟨huCut, huComp⟩
  rcases hvD with ⟨hvCut, hvComp⟩
  have huK : uC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact huCut (by simp [tailClusterCut, hmem])
  have hvK : vC.1 ∉ (K : Set (Site d)) := by
    intro hmem
    exact hvCut (by simp [tailClusterCut, hmem])
  refine ⟨huK, hvK, ?_⟩
  have hreach :
      ((tailClusterGraph omega x).induce
        ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ).Reachable
          ⟨uC, huCut⟩ ⟨vC, hvCut⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact huComp.trans hvComp.symm
  let f0 : {z : tailClusterVertex omega x //
      z ∈ ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ} →
      {z : Site d // z ∈ (K : Set (Site d))ᶜ} := fun z =>
    ⟨z.1.1, by
      intro hzK
      exact z.2 (by simp [tailClusterCut, hzK])⟩
  let f : ((tailClusterGraph omega x).induce
      ((tailClusterCut omega x K : Set (tailClusterVertex omega x)))ᶜ) →g
      ((openSubgraph d omega).induce (K : Set (Site d))ᶜ) := {
    toFun := f0
    map_rel' := by
      intro a b hab
      exact hab
  }
  exact hreach.map f


theorem infiniteCluster_has_tail_outside_finset
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d)) :
    ∃ T : Set (Site d), T.Infinite ∧ T ⊆ cluster d omega x ∧
      (∀ u ∈ T, ∀ v ∈ T,
        ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩) := by
  obtain ⟨D, hD⟩ := infiniteCluster_component_after_finset omega x hinf K
  exact ⟨tailComponentSites omega x K D,
    tailComponentSites_infinite omega x K D hD,
    tailComponentSites_subset_cluster omega x K D,
    tailComponentSites_connected_outside omega x K D⟩


theorem infiniteCluster_has_open_exit_to_infinite_tail
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d omega x).Infinite) (K : Finset (Site d))
    (hxK : x ∈ K) :
    ∃ u v : Site d, ∃ T : Set (Site d),
      u ∈ K ∧ v ∉ K ∧ (openSubgraph d omega).Adj u v ∧ v ∈ T ∧
      T.Infinite ∧ T ⊆ cluster d omega x ∧
      (∀ a ∈ T, ∀ b ∈ T,
        ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
          ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
            ⟨a, ha⟩ ⟨b, hb⟩) := by
  obtain ⟨D, hD⟩ := infiniteCluster_component_after_finset omega x hinf K
  have hcut : (tailClusterCut omega x K).Nonempty := by
    refine ⟨⟨x, self_mem_cluster omega x⟩, ?_⟩
    simp [tailClusterCut, hxK]
  obtain ⟨⟨v, u⟩, hvD, huCut, hadj⟩ :=
    D.exists_adj_boundary_pair (tailClusterGraphPreconnected omega x).out hcut
  have huK : u.1 ∈ K := by
    simpa [tailClusterCut] using huCut
  have hvK : v.1 ∉ K := by
    intro hv
    exact D.notMem_of_mem hvD (by simp [tailClusterCut, hv])
  refine ⟨u.1, v.1, tailComponentSites omega x K D,
    huK, hvK, hadj.symm, ⟨v, hvD, rfl⟩, ?_, ?_, ?_⟩
  · exact tailComponentSites_infinite omega x K D hD
  · exact tailComponentSites_subset_cluster omega x K D
  · exact tailComponentSites_connected_outside omega x K D


end StatMech.Percolation
