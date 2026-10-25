/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part10
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


@[simp] theorem mem_frpCrossingWindow (K : FiniteRangeKernel d) (n : ℕ)
    (x : Site d) :
    x ∈ frpCrossingWindow K n ↔ x ∈ box d ((n - 1) + K.range) := by
  rw [frpCrossingWindow, Set.Finite.mem_toFinset]


theorem frpCrossingEvent_eq_finite (K : FiniteRangeKernel d) (n : ℕ) :
    frpCrossingEvent K n =
      connEvent (frpGraph K) (frpCrossingWindow K n : Set (Site d))
        (0 : Site d) (box d (n - 1))ᶜ := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    have h0 : (0 : Site d) ∈ (box_finite d (n - 1)).toFinset := by
      rw [Set.Finite.mem_toFinset, mem_box]
      intro i
      simp
    have hfirst := frp_firstExit_inclusion K Set.univ
      (box_finite d (n - 1)).toFinset (box d (n - 1))ᶜ
      (0 : Site d) h0 (by simp)
    obtain ⟨q, hq, htriple⟩ := Set.mem_iUnion₂.mp (hfirst homega)
    have hparts := disjointOccurrence_subset_inter _ _ htriple
    have htail := disjointOccurrence_subset_inter _ _ hparts.2
    rcases hparts.1 with ⟨h0S, x, hxS, hxeq, hconn⟩
    simp only [Set.mem_singleton_iff] at hxeq
    subst x
    have hqmem := (mem_frpBoundaryPairs K
      (box_finite d (n - 1)).toFinset).mp hq
    have hxbox : q.1 ∈ box d (n - 1) := by
      simpa [Set.Finite.mem_toFinset] using hqmem.1
    have hybox : q.2 ∈ box d ((n - 1) + K.range) :=
      frp_adj_mem_box_add K hxbox hqmem.2.2
    have hSsub : (box d (n - 1)) ⊆ box d ((n - 1) + K.range) :=
      box_mono d (Nat.le_add_right _ _)
    have hSsub' : ((box_finite d (n - 1)).toFinset : Set (Site d)) ⊆
        (frpCrossingWindow K n : Set (Site d)) := by
      intro z hz
      rw [Finset.mem_coe, mem_frpCrossingWindow]
      apply hSsub
      simpa [Set.Finite.mem_toFinset] using hz
    have hconn' := frp_connWithin_mono_set K omega hSsub' hconn
    have hedge : (openSub (frpGraph K) omega).Adj q.1 q.2 :=
      ⟨hqmem.2.2, htail.1⟩
    have hxwin : q.1 ∈ frpCrossingWindow K n :=
      (mem_frpCrossingWindow K n q.1).mpr (hSsub hxbox)
    have hywin : q.2 ∈ frpCrossingWindow K n :=
      (mem_frpCrossingWindow K n q.2).mpr hybox
    have hedge' : ((openSub (frpGraph K) omega).induce
        (frpCrossingWindow K n : Set (Site d))).Adj
        ⟨q.1, hxwin⟩ ⟨q.2, hywin⟩ := hedge
    have hyout : q.2 ∈ (box d (n - 1))ᶜ := by
      rw [Set.mem_compl_iff]
      intro hyin
      exact hqmem.2.1 (by simpa [Set.Finite.mem_toFinset] using hyin)
    refine ⟨?_, q.2, ?_, hyout, hconn'.trans hedge'.reachable⟩
    · rw [Finset.mem_coe, mem_frpCrossingWindow, mem_box]
      intro i
      simp
    · exact_mod_cast hywin
  · rintro omega ⟨h0, z, hz, hzout, hconn⟩
    refine ⟨Set.mem_univ _, z, Set.mem_univ _, hzout, ?_⟩
    exact frp_connWithin_mono_set K omega (Set.subset_univ _) hconn


theorem frpCrossingEvent_dependsOn (K : FiniteRangeKernel d) (n : ℕ) :
    DependsOn (frpCrossingEvent K n)
      (frpInternalEdges (frpCrossingWindow K n) : Set (Sym2 (Site d))) := by
  rw [frpCrossingEvent_eq_finite]
  exact frp_connEvent_set_dependsOn K (frpCrossingWindow K n)
    (0 : Site d) (box d (n - 1))ᶜ


end Sharpness
end StatMech
