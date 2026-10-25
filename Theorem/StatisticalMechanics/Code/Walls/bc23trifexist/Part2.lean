/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Def.StatisticalMechanics.Code.Walls.bc23trifexist
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc23_mem_walkEdges {a b : Site d} (w : (hypercubicLattice d).Walk a b)
    {e : Sym2 (Site d)} (he : e ∈ w.edges) : e ∈ bc23_walkEdges w := by
  rw [bc23_walkEdges, List.mem_toFinset]; exact he


theorem bc23_corridor_of_walk_subset (G : Finset (Sym2 (Site d))) {a b : Site d}
    (w : (hypercubicLattice d).Walk a b)
    (hsub : bc23_walkEdges w ⊆ G) (h0 : (0 : Site d) ∉ w.support) :
    Relation.ReflTransGen (CorridorStep G) a b :=
  bc23_corridor_of_walk G w (fun e he => hsub (bc23_mem_walkEdges w he)) h0


theorem bc23_mengerCore_of_corridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) (w₁ w₂ w₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hcor : Relation.ReflTransGen (CorridorStep G) a₁ w₁ ∧
      Relation.ReflTransGen (CorridorStep G) a₂ w₂ ∧
      Relation.ReflTransGen (CorridorStep G) a₃ w₃)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
    (hdist : cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) w₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) w₃) :
    MengerCore ω :=
  ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, hcor, hinf, hdist⟩


theorem bc23_removeSite_le_forceOpen (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset G ω) := by
  have h := bma_removeSite_forceOpen_mono_sub (ω := ω) (Wⱼ := (∅ : Finset (Sym2 (Site d))))
    (W := G) (Finset.empty_subset G)
  rwa [mng_forceOpenFinset_empty] at h


theorem bc23_forcedCluster_infinite_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (b : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω b) (hinf : (cluster d ω b).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset G ω)) b).Infinite :=
  (bc20_removeSite_infinite_of_originFree ω b h0 hinf).mono
    (cluster_mono (bc23_removeSite_le_forceOpen ω G) b)


theorem bc23_mengerCore_of_latticeCorridors (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (w₁ : (hypercubicLattice d).Walk a₁ b₁) (w₂ : (hypercubicLattice d).Walk a₂ b₂)
    (w₃ : (hypercubicLattice d).Walk a₃ b₃)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hw0₁ : (0 : Site d) ∉ w₁.support) (hw0₂ : (0 : Site d) ∉ w₂.support)
    (hw0₃ : (0 : Site d) ∉ w₃.support)
    (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
      (0 : Site d) ∉ cluster d ω b₃)
    (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
    (S₁ S₂ S₃ : Set (Site d))
    (hb₁ : b₁ ∈ S₁) (hb₂ : b₂ ∈ S₂) (hb₃ : b₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset
        (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃) :
    MengerCore ω := by
  classical
  set G : Finset (Sym2 (Site d)) :=
    bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃ with hG
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  
  have hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ b₁ :=
    bc23_corridor_of_walk_subset G w₁
      (by intro e he; rw [hG, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inl he)) hw0₁
  have hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ b₂ :=
    bc23_corridor_of_walk_subset G w₂
      (by intro e he; rw [hG, Finset.mem_union, Finset.mem_union]; exact Or.inl (Or.inr he)) hw0₂
  have hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ b₃ :=
    bc23_corridor_of_walk_subset G w₃
      (by intro e he; rw [hG, Finset.mem_union]; exact Or.inr he) hw0₃
  
  have hinf₁ : (cluster d ϱ b₁).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₁ h0.1 hinf.1
  have hinf₂ : (cluster d ϱ b₂).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₂ h0.2.1 hinf.2.1
  have hinf₃ : (cluster d ϱ b₃).Infinite := bc23_forcedCluster_infinite_of_originFree ω G b₃ h0.2.2 hinf.2.2
  
  have hsub₁ : cluster d ϱ b₁ ⊆ S₁ := cluster_subset_of_adjClosed ϱ S₁ b₁ hb₁ hcl₁
  have hsub₂ : cluster d ϱ b₂ ⊆ S₂ := cluster_subset_of_adjClosed ϱ S₂ b₂ hb₂ hcl₂
  have hsub₃ : cluster d ϱ b₃ ⊆ S₃ := cluster_subset_of_adjClosed ϱ S₃ b₃ hb₃ hcl₃
  exact bc23_mengerCore_of_corridors ω a₁ a₂ a₃ G b₁ b₂ b₃ hne hadj
    ⟨hcor₁, hcor₂, hcor₃⟩ ⟨hinf₁, hinf₂, hinf₃⟩
    ⟨cluster_ne_of_disjoint ϱ b₁ b₂ S₁ S₂ hsub₁ hsub₂ hd12,
      cluster_ne_of_disjoint ϱ b₁ b₃ S₁ S₃ hsub₁ hsub₃ hd13,
      cluster_ne_of_disjoint ϱ b₂ b₃ S₂ S₃ hsub₂ hsub₃ hd23⟩


end StatMech.Walls
