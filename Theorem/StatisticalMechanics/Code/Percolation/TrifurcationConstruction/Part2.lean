/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Def.StatisticalMechanics.Code.Percolation.TrifurcationConstruction
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem precursor_subset_force_trif (a₁ a₂ a₃ : Site d) :
    NeighborTrifPrecursor d a₁ a₂ a₃ ⊆
      (fun ω => forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω)
        ⁻¹' {ω | IsTrifurcation d ω 0} := by
  rintro ω ⟨hne, ⟨hadj1, hadj2, hadj3⟩, ⟨hinf1, hinf2, hinf3⟩, ⟨hsep12, hsep13, hsep23⟩⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  exact isTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj1 hadj2 hadj3 hinf1 hinf2 hinf3
    hsep12 hsep13 hsep23


theorem trif_pos_of_precursor_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | IsTrifurcation d ω 0} := by
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  by_contra h
  rw [not_lt, nonpos_iff_eq_zero] at h
  
  have hac : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ := hfe F
  have hpush : (μ.map (fun ω => forceOpenFinset F ω)) {ω | IsTrifurcation d ω 0}
      = μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) :=
    Measure.map_apply (measurable_forceOpenFinset F) (measurableSet_isTrifurcation 0)
  have hpre0 : μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) = 0 := by
    rw [← hpush]; exact hac h
  have hAle : μ (NeighborTrifPrecursor d a₁ a₂ a₃)
      ≤ μ ((fun ω => forceOpenFinset F ω) ⁻¹' {ω | IsTrifurcation d ω 0}) :=
    measure_mono (precursor_subset_force_trif a₁ a₂ a₃)
  rw [hpre0] at hAle
  exact absurd (le_antisymm hAle bot_le) (ne_of_gt hpos)


theorem exists_three_distinct {α : Type*} {S : Set α} (h : S.encard = ⊤) :
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have h3 : (3 : ℕ∞) ≤ S.encard := by rw [h]; exact le_top
  obtain ⟨t, hts, ht3⟩ := Set.exists_subset_encard_eq h3
  rw [Set.encard_eq_three] at ht3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht3
  exact ⟨a, b, c, hts (by simp), hts (by simp), hts (by simp), hab, hac, hbc⟩


end Percolation
end StatMech
