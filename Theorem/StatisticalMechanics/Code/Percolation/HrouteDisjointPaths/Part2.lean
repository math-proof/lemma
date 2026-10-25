/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Def.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem corridorWorks_subset_force_precursor (a₁ a₂ a₃ : Site d)
    (G : Finset (Sym2 (Site d))) :
    CorridorWorks a₁ a₂ a₃ G ⊆
      (fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃ := by
  rintro ω ⟨hne, hadj, hinf, hd12, hd13, hd23⟩
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hc; exact hd12 (cluster_eq_of_connected hc)
  · intro hc; exact hd13 (cluster_eq_of_connected hc)
  · intro hc; exact hd23 (cluster_eq_of_connected hc)


theorem cluster_subset_of_adjClosed (ϱ : ConfigSpace (Sym2 (Site d)))
    (S : Set (Site d)) (a : Site d) (ha : a ∈ S)
    (hclosed : ∀ u v, u ∈ S → (openSubgraph d ϱ).Adj u v → v ∈ S) :
    cluster d ϱ a ⊆ S := by
  intro y hy
  rw [mem_cluster] at hy
  unfold Connected at hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  induction hy with
  | refl => exact ha
  | @tail b c _ hbc ih => exact hclosed b c ih hbc


theorem cluster_ne_of_disjoint (ϱ : ConfigSpace (Sym2 (Site d))) (a b : Site d)
    (S T : Set (Site d)) (hS : cluster d ϱ a ⊆ S) (hT : cluster d ϱ b ⊆ T)
    (hdisj : Disjoint S T) : cluster d ϱ a ≠ cluster d ϱ b := by
  intro heq
  have ha : a ∈ cluster d ϱ a := self_mem_cluster ϱ a
  have ha' : a ∈ cluster d ϱ b := heq ▸ ha
  have hmem : a ∈ S ∩ T := ⟨hS ha, hT ha'⟩
  rw [Set.disjoint_iff_inter_eq_empty] at hdisj
  rw [hdisj] at hmem
  exact absurd hmem (Set.notMem_empty a)


theorem corridorWorks_of_separated (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d)))
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (S₁ S₂ S₃ : Set (Site d))
    (hmem₁ : a₁ ∈ S₁) (hmem₂ : a₂ ∈ S₂) (hmem₃ : a₃ ∈ S₃)
    (hcl₁ : ∀ u v, u ∈ S₁ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
    (hcl₂ : ∀ u v, u ∈ S₂ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
    (hcl₃ : ∀ u v, u ∈ S₃ →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
    (hd12 : Disjoint S₁ S₂) (hd13 : Disjoint S₁ S₃) (hd23 : Disjoint S₂ S₃)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) :
    ω ∈ CorridorWorks a₁ a₂ a₃ G := by
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  have hsub₁ : cluster d ϱ a₁ ⊆ S₁ := cluster_subset_of_adjClosed ϱ S₁ a₁ hmem₁ hcl₁
  have hsub₂ : cluster d ϱ a₂ ⊆ S₂ := cluster_subset_of_adjClosed ϱ S₂ a₂ hmem₂ hcl₂
  have hsub₃ : cluster d ϱ a₃ ⊆ S₃ := cluster_subset_of_adjClosed ϱ S₃ a₃ hmem₃ hcl₃
  exact ⟨hne, hadj, hinf,
    cluster_ne_of_disjoint ϱ a₁ a₂ S₁ S₂ hsub₁ hsub₂ hd12,
    cluster_ne_of_disjoint ϱ a₁ a₃ S₁ S₃ hsub₁ hsub₃ hd13,
    cluster_ne_of_disjoint ϱ a₂ a₃ S₂ S₃ hsub₂ hsub₃ hd23⟩


end DisjointPaths
end Percolation
end StatMech
