/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose2
import Theorem.StatisticalMechanics.Code.FK.SecantClose.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.Strassen
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


theorem fuc_real_preimage_eq_indicator_sum {α β : Type*} [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (A : Set β) :
    μ.real (f ⁻¹' A) = ∑ ω : β, A.indicator (fun _ => (1 : ℝ)) ω * μ.real (f ⁻¹' {ω}) := by
  classical
  have hpre : f ⁻¹' A = ⋃ ω ∈ (Finset.univ.filter (· ∈ A)), f ⁻¹' {ω} := by
    ext x; simp [Set.mem_preimage]
  rw [hpre, measureReal_biUnion_finset]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  · intro a _ b _ hab
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hxa hxb
    exact hab (hxa ▸ hxb)
  · intro ω _; exact hf (measurableSet_singleton ω)


theorem fuc_sum_real_preimage_eq_one {α β : Type*} [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f) :
    ∑ ω : β, μ.real (f ⁻¹' {ω}) = 1 := by
  classical
  have h : (∑ ω : β, μ.real (f ⁻¹' {ω})) = μ.real (f ⁻¹' (univ : Set β)) := by
    have hpre : (f ⁻¹' (univ : Set β)) = ⋃ ω : β, f ⁻¹' {ω} := by ext x; simp
    rw [hpre, measureReal_iUnion_fintype
      (by intro i j hij; apply Set.disjoint_left.mpr; intro x h1 h2; simp_all)
      (fun ω => hf (measurableSet_singleton ω))]
  rw [h]; simp [measureReal_def]


variable {E : Type*} [Fintype E] [DecidableEq E]


theorem fuc_measOfMass_real_singleton {μ : ConfigSpace E → ℝ} (hμ : 0 ≤ μ)
    (x : ConfigSpace E) : (measOfMass μ).real {x} = μ x := by
  classical
  rw [measOfMass_real μ hμ {x}, Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [Set.mem_singleton_iff, hb]
  · intro h; exact absurd (Finset.mem_univ x) h


theorem fuc_isMonotoneCouplingFun_of_monotoneCoupling {μ ν : ConfigSpace E → ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    {κ : Measure (ConfigSpace E × ConfigSpace E)} [IsFiniteMeasure κ]
    (hcoup : MonotoneCoupling (measOfMass μ) (measOfMass ν) κ) :
    IsMonotoneCouplingFun (fun z => κ.real {z}) μ ν := by
  classical
  refine ⟨fun z => measureReal_nonneg, ?_, ?_, ?_⟩
  · 
    intro z hz
    have hmem : z ∈ (orderSet E)ᶜ := hz
    have hle : κ {z} ≤ κ (orderSet E)ᶜ :=
      measure_mono (by
        intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hmem)
    rw [hcoup.supported] at hle
    simp only [measureReal_def]
    rw [le_antisymm hle bot_le]; simp
  · 
    intro ω
    have hfib : (∑ ω' : ConfigSpace E, κ.real {(ω, ω')}) = κ.fst.real {ω} := by
      rw [measureReal_def, Measure.fst_apply (measurableSet_singleton ω)]
      have hpre : (Prod.fst ⁻¹' {ω} : Set (ConfigSpace E × ConfigSpace E))
          = ⋃ ω' : ConfigSpace E, {(ω, ω')} := by ext ⟨a, b⟩; simp [Set.mem_preimage, eq_comm]
      rw [hpre, measure_iUnion
        (by intro i j hij; apply Set.disjoint_left.mpr; rintro ⟨a, b⟩ h1 h2; simp_all)
        (fun ω' => measurableSet_singleton _)]
      rw [tsum_fintype, ENNReal.toReal_sum (fun ω' _ => measure_ne_top κ _)]; rfl
    rw [hfib, hcoup.fst_eq, fuc_measOfMass_real_singleton hμ ω]
  · 
    intro ω'
    have hfib : (∑ ω : ConfigSpace E, κ.real {(ω, ω')}) = κ.snd.real {ω'} := by
      rw [measureReal_def, Measure.snd_apply (measurableSet_singleton ω')]
      have hpre : (Prod.snd ⁻¹' {ω'} : Set (ConfigSpace E × ConfigSpace E))
          = ⋃ ω : ConfigSpace E, {(ω, ω')} := by ext ⟨a, b⟩; simp [Set.mem_preimage, eq_comm]
      rw [hpre, measure_iUnion
        (by intro i j hij; apply Set.disjoint_left.mpr; rintro ⟨a, b⟩ h1 h2; simp_all)
        (fun ω => measurableSet_singleton _)]
      rw [tsum_fintype, ENNReal.toReal_sum (fun ω _ => measure_ne_top κ _)]; rfl
    rw [hfib, hcoup.snd_eq, fuc_measOfMass_real_singleton hν ω']


theorem fuc_isMonotoneCouplingFun_of_dominated {μ ν : ConfigSpace E → ℝ}
    (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hnμ : ∑ ω, μ ω = 1) (hnν : ∑ ω, ν ω = 1)
    (hdom : measOfMass μ ≼ measOfMass ν) :
    ∃ P : ConfigSpace E × ConfigSpace E → ℝ, IsMonotoneCouplingFun P μ ν := by
  have hpμ : IsProbabilityMeasure (measOfMass μ) := measOfMass_isProbabilityMeasure μ hμ hnμ
  have hpν : IsProbabilityMeasure (measOfMass ν) := measOfMass_isProbabilityMeasure ν hν hnν
  obtain ⟨κ, hκfin, hκ⟩ :=
    StatMech.exists_monotoneCoupling_of_stochasticallyDominated _ _ hdom
  exact ⟨fun z => κ.real {z}, fuc_isMonotoneCouplingFun_of_monotoneCoupling hμ hν hκ⟩


end FK
end StatMech
