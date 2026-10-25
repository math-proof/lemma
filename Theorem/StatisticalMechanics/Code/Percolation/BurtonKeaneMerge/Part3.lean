/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem mergeWitness_subset_force_lt (F : Finset (Sym2 (Site d))) {k : ℕ∞} (hk : k ≠ ⊤) :
    MergeWitness d F k ⊆
      (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k} := by
  intro ω hω
  obtain ⟨hkeq, x, y, hx, hy, hne, hmerge⟩ := hω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfin : numInfiniteClusters d ω ≠ ⊤ := by rw [hkeq]; exact hk
  have := numInfiniteClusters_lt_of_merge F ω hfin x y hx hy hne hmerge
  rwa [hkeq] at this


theorem measurableSet_numInfiniteClusters_lt (k : ℕ∞) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < k} :=
  measurable_numInfiniteClusters (MeasurableSet.of_discrete)


theorem numInfiniteClusters_lt_null
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    μ {ω | numInfiniteClusters d ω < k} = 0 := by
  have hdisj : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω < k}ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]; exact lt_irrefl k
  have hfull : μ {ω | numInfiniteClusters d ω < k}ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hdisj)
  exact (prob_compl_eq_one_iff (measurableSet_numInfiniteClusters_lt k)).mp hfull


end Percolation
end StatMech
