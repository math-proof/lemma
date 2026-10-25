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
import Def.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem iEqTop_subset_iUnion_threeMeetBox :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ⊆ ⋃ n, threeMeetBox d n := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  have hcard : (infiniteClusters d ω).encard = ⊤ := hω
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h12, h13, h23⟩ := exists_three_distinct hcard
  simp only [infiniteClusters, Set.mem_setOf_eq] at hC₁ hC₂ hC₃
  obtain ⟨hinf1, x, hxeq⟩ := hC₁
  obtain ⟨hinf2, y, hyeq⟩ := hC₂
  obtain ⟨hinf3, z, hzeq⟩ := hC₃
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hzinf : (cluster d ω z).Infinite := by rw [← hzeq]; exact hinf3
  have hcl12 : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact h12
  have hcl13 : cluster d ω x ≠ cluster d ω z := by rw [← hxeq, ← hzeq]; exact h13
  have hcl23 : cluster d ω y ≠ cluster d ω z := by rw [← hyeq, ← hzeq]; exact h23
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y, z} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (by simp)
  have hybox : y ∈ box d n := hn (by simp)
  have hzbox : z ∈ box d n := hn (by simp)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, z, hxbox, hybox, hzbox, hxinf, hyinf, hzinf,
    hcl12, hcl13, hcl23⟩


theorem exists_threeMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hpos : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
    ∃ n : ℕ, 0 < μ (threeMeetBox d n) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ n, threeMeetBox d n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, threeMeetBox d n) ≤ ∑' n, μ (threeMeetBox d n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = ⊤}
      ≤ μ (⋃ n, threeMeetBox d n) :=
    measure_mono iEqTop_subset_iUnion_threeMeetBox
  rw [hunion0] at hle
  exact absurd (le_antisymm hle bot_le) (ne_of_gt hpos)


theorem htrif_discharged
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0} := by
  intro htop
  obtain ⟨n, hn⟩ := exists_threeMeetBox_pos μ htop
  obtain ⟨a₁, a₂, a₃, hpre⟩ := hroute n hn
  exact trif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpre


theorem burton_keane_uniqueness_trif_route
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_full μ herg hfe bdry hbound hvol hdens
    (htrif_discharged μ hfe hroute)

end Percolation
end StatMech
