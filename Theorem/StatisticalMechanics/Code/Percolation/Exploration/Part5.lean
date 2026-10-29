/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.Exploration.Part5
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem mem_incidentWithinFinset {K S : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ incidentWithinFinset K S ↔ ∃ x ∈ K, ∃ y ∈ S, e = s(x, y) := by
  simp only [incidentWithinFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩; exact ⟨x, hx, y, hy, he.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩


theorem incidentWithinFinset_coe (K S : Finset (Site d)) :
    (incidentWithinFinset K S : Set (Sym2 (Site d)))
      = incidentWithin (K : Set _) (S : Set _) := by
  ext e
  rw [Finset.mem_coe, mem_incidentWithinFinset]
  simp only [incidentWithin, Set.mem_setOf_eq, Finset.mem_coe]


theorem clusterEvent_dependsOn {S : Finset (Site d)} {o : Site d} {K : Finset (Site d)}
    (hoS : o ∈ (S : Set (Site d))) :
    DependsOn ((clusterEvent d (S : Set (Site d)) o (K : Set (Site d))).indicator
      (fun _ => (1 : ℝ))) (incidentWithinFinset K S : Set (Sym2 (Site d))) := by
  intro ω ω' h
  rw [incidentWithinFinset_coe] at h
  have hiff := clusterEvent_iff (K := (K : Set (Site d))) hoS (fun e he => h e he)
  by_cases hω : ω ∈ clusterEvent d (S : Set (Site d)) o (K : Set (Site d))
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]


theorem exploration_decomposition (p : NNReal) (hp : p ≤ 1)
    (S : Finset (Site d)) (o : Site d) (hoS : o ∈ (S : Set (Site d))) (K : Finset (Site d))
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (incidentWithinFinset K S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterEvent d (S : Set (Site d)) o (K : Set (Site d)) ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) o (K : Set (Site d)))
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  indep_cylinder_inf p hp _ B (incidentWithinFinset K S) U hdisj
    (clusterEvent_dependsOn hoS) hB

end Percolation
end StatMech
