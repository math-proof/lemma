/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BKUniqueness2
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem merge_contradiction
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (F : Finset (Sym2 (Site d)))
    (hfe : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ)
    {A : Set (ConfigSpace (Sym2 (Site d)))}
    (hApos : 0 < μ A)
    (hAsub : A ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :
    False := by
  have hnullset := numInfiniteClusters_lt_null μ hk
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | numInfiniteClusters d ω < k}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :=
    Measure.map_apply (measurable_forceOpenFinset F) (measurableSet_numInfiniteClusters_lt k)
  have hpre0 :
      μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) = 0 := by
    rw [← hpush]; exact hfe hnullset
  have hAle :
      μ A ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :=
    measure_mono hAsub
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hApos)


theorem burton_keane_merge_excludes_finite_ge_two
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → 2 ≤ k → k = ⊤ := by
  intro k hk hk2
  by_contra hktop
  obtain ⟨F, hFpos⟩ := hmergeGeom k hk2 hktop hk
  exact merge_contradiction μ hk F (hfe F) hFpos (mergeWitness_subset_force_lt F hktop)


theorem merge_event_null
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤)
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    μ (atLeastTwoInfinite d) = 0 := by
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  have hktop : k ≠ ⊤ := hkne_top k hk
  
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    exact hktop (burton_keane_merge_excludes_finite_ge_two μ hfe hmergeGeom k hk h2)
  
  have hkle : k ≤ 1 := enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆ (atLeastTwoInfinite d)ᶜ := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [atLeastTwoInfinite_compl]
    simp only [Set.mem_setOf_eq, hω]; exact hkle
  have hfull : μ (atLeastTwoInfinite d)ᶜ = 1 := le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  exact (prob_compl_eq_one_iff measurableSet_atLeastTwoInfinite).mp hfull


theorem burton_keane_uniqueness_via_merge
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0})
    (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 →
      ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  
  have hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
    intro k hk
    obtain ⟨k', hk'top, hk'⟩ :=
      numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif
    
    intro hktop
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ {ω | numInfiniteClusters d ω = k'}ᶜ := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hω]
      intro h; exact hk'top (by rw [← h, hktop])
    have hmk' : MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'} := by
      have heq : {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k'}
          = numInfiniteClusters d ⁻¹' {k'} := by ext ω; simp [Set.mem_preimage]
      rw [heq]; exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
    have hfull : μ {ω | numInfiniteClusters d ω = k'}ᶜ = 1 :=
      le_antisymm prob_le_one (hk ▸ measure_mono hsub)
    have hnull : μ {ω | numInfiniteClusters d ω = k'} = 0 :=
      (prob_compl_eq_one_iff hmk').mp hfull
    rw [hk'] at hnull
    exact one_ne_zero hnull
  
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    merge_event_null μ herg hfe hkne_top hmergeGeom
  
  refine ⟨numInfiniteClusters_zero_or_one μ herg hmerge, hmerge,
    infiniteCluster_unique_ae μ herg hmerge⟩

end Percolation
end StatMech
