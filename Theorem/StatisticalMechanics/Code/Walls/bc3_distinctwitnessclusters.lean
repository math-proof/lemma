/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_cutClusterEq_of_originNotMem (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω x) :
    cluster d (removeSite 0 ω) x = cluster d ω x := by
  apply Set.Subset.antisymm
  · exact ctc2_cluster_removeSite_subset 0 x ω
  · intro y hy
    rw [mem_cluster] at hy ⊢
    obtain ⟨w⟩ := hy
    
    have havoid : (0 : Site d) ∉ w.support := fun hmem =>
      h0 (mem_cluster.mpr (w.takeUntil 0 hmem).reachable)
    exact pap_connected_removeSite_of_walk_avoid ω 0 w havoid


theorem bc3_cutClusterInfinite_of_originNotMem (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (h0 : (0 : Site d) ∉ cluster d ω x) :
    (cluster d (removeSite 0 ω) x).Infinite := by
  rw [bc3_cutClusterEq_of_originNotMem ω x h0]; exact hinf


theorem bc3_clusterEq_of_originMem (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hx : (0 : Site d) ∈ cluster d ω x) (hy : (0 : Site d) ∈ cluster d ω y) :
    cluster d ω x = cluster d ω y :=
  (cluster_eq_of_connected (mem_cluster.mp hx)).trans
    (cluster_eq_of_connected (mem_cluster.mp hy)).symm


theorem bc3_twoArms_avoid_origin (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₂) ∨
      ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₃) ∨
      ((0 : Site d) ∉ cluster d ω x₂ ∧ (0 : Site d) ∉ cluster d ω x₃) := by
  by_cases h1 : (0 : Site d) ∈ cluster d ω x₁
  · 
    exact Or.inr (Or.inr ⟨fun h2 => hd12 (bc3_clusterEq_of_originMem ω h1 h2),
      fun h3 => hd13 (bc3_clusterEq_of_originMem ω h1 h3)⟩)
  · by_cases h2 : (0 : Site d) ∈ cluster d ω x₂
    · 
      exact Or.inr (Or.inl ⟨h1, fun h3 => hd23 (bc3_clusterEq_of_originMem ω h2 h3)⟩)
    · exact Or.inl ⟨h1, h2⟩


theorem bc3_twoArms_cutInfinite (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite) ∨
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∨
      ((cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
  rcases bc3_twoArms_avoid_origin ω hd12 hd13 hd23 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 b⟩
  · exact Or.inr (Or.inl ⟨bc3_cutClusterInfinite_of_originNotMem ω x₁ hi1 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 b⟩)
  · exact Or.inr (Or.inr ⟨bc3_cutClusterInfinite_of_originNotMem ω x₂ hi2 a,
      bc3_cutClusterInfinite_of_originNotMem ω x₃ hi3 b⟩)


end Walls
end StatMech
