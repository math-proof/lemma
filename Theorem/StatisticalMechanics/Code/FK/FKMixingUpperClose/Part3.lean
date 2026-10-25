/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Def.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part3
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_selfMixing_one_of_pairMixing [Countable E] (hmix : fmu_PairMixing (G := G) μ)
    {C : Set (ConfigSpace E)} (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : G, |μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
        - (μ.real C) ^ 2| < ε := by
  classical
  set W := ∑ T ∈ P, ∑ T' ∈ P, |c T * c T'| with hW
  have hWnn : 0 ≤ W := by
    apply Finset.sum_nonneg; intro T hT; apply Finset.sum_nonneg; intro T' hT'; positivity
  set δ := ε / (W + 1) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨g, hg⟩ := hmix P δ hδpos
  refine ⟨g, ?_⟩
  rw [fmu_real_inter_shift_eq_sum g hC P c hexp]
  have hsq : (μ.real C) ^ 2 = ∑ T ∈ P, ∑ T' ∈ P,
      c T * c T' * (μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')) := by
    rw [show (μ.real C) ^ 2 = μ.real C * μ.real C from sq _]
    rw [fmu_real_eq_sum hC P c hexp, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro T hT
    apply Finset.sum_congr rfl; intro T' hT'; ring
  rw [hsq, ← Finset.sum_sub_distrib]
  have hdiff : ∀ T : Finset E,
      (∑ T' ∈ P, c T * c T' *
        μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T'))
      - (∑ T' ∈ P, c T * c T' * (μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')))
      = ∑ T' ∈ P, c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')) := by
    intro T
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro T' hT'; ring
  simp_rw [hdiff]
  calc |∑ T ∈ P, ∑ T' ∈ P, c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T'))|
      ≤ ∑ T ∈ P, ∑ T' ∈ P, |c T * c T' *
          (μ.real (fmu_multiOpen T ∩
              (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
            - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T'))| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum; intro T hT
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ P, ∑ T' ∈ P, |c T * c T'| * δ := by
        apply Finset.sum_le_sum; intro T hT
        apply Finset.sum_le_sum; intro T' hT'
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (le_of_lt (hg T hT T' hT')) (abs_nonneg _)
    _ = W * δ := by
        rw [hW, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro T hT
        rw [Finset.sum_mul]
    _ < ε := by
        rw [hδ]
        have hW1 : (W + 1) ≠ 0 := by positivity
        have hdpos : (0:ℝ) < ε / (W + 1) := by positivity
        calc W * (ε / (W + 1)) < (W+1) * (ε / (W+1)) :=
              mul_lt_mul_of_pos_right (by linarith) hdpos
          _ = ε := mul_div_cancel₀ ε hW1


theorem fmu_selfMixing_of_pairMixing [Countable E] (hmix : fmu_PairMixing (G := G) μ) :
    fmc_SelfMixing (G := G) μ := by
  classical
  intro A hA ε hε
  obtain ⟨P, c, hexp⟩ := fmu_cylinder_expand A hA
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  exact fmu_selfMixing_one_of_pairMixing hmix hAmeas P c hexp ε hε


theorem fmu_isErgodic_of_pairMixing [Countable E]
    (hμ : IsTranslationInvariant (G := G) μ) (hmix : fmu_PairMixing (G := G) μ) :
    IsErgodic (G := G) μ :=
  fmc_isErgodic_of_selfMixing hμ (fmu_selfMixing_of_pairMixing hmix)


theorem fmu_dirac_mem (g : G) (T T' : Finset E) :
    (fun _ : E => true) ∈ fmu_multiOpen T ∩
      (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T' := by
  refine ⟨?_, ?_⟩
  · intro e he; rfl
  · intro e he; rfl


theorem fmu_pairMixing_dirac [Countable E] [MeasurableSingletonClass (ConfigSpace E)] :
    fmu_PairMixing (G := G) (Measure.dirac (fun _ : E => true)) := by
  intro P δ hδ
  refine ⟨1, ?_⟩
  intro T hT T' hT'
  
  have hmem1 : (fun _ : E => true) ∈ fmu_multiOpen T := fun e he => rfl
  have hmem2 : (fun _ : E => true) ∈ fmu_multiOpen T' := fun e he => rfl
  have hmemI : (fun _ : E => true) ∈ fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T' :=
    fmu_dirac_mem 1 T T'
  have hmeasT : MeasurableSet (fmu_multiOpen T) := fmu_multiOpen_measurable T
  have hmeasT' : MeasurableSet (fmu_multiOpen T') := fmu_multiOpen_measurable T'
  have hmeasI : MeasurableSet (fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') :=
    hmeasT.inter (hmeasT'.preimage (measurable_shift 1))
  have e1 : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T) = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT, Set.indicator_of_mem hmem1]; simp
  have e2 : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasT', Set.indicator_of_mem hmem2]; simp
  have eI : (Measure.dirac (fun _ : E => true)).real (fmu_multiOpen T ∩
      (shift (1 : G) : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') = 1 := by
    rw [Measure.real, MeasureTheory.Measure.dirac_apply' _ hmeasI, Set.indicator_of_mem hmemI]; simp
  rw [e1, e2, eI]; simpa using hδ


theorem fmu_multiOpen_mem_measurableCylinders [DecidableEq E] (T : Finset E) :
    fmu_multiOpen T ∈ measurableCylinders (fun _ : E => Bool) := by
  rw [mem_measurableCylinders]
  refine ⟨T, {σ : (↥T → Bool) | ∀ e, σ e = true}, MeasurableSet.of_discrete, ?_⟩
  ext ω
  simp only [fmu_multiOpen, Set.mem_setOf_eq, mem_cylinder, Finset.restrict_def]
  exact ⟨fun h e => h e.1 e.2, fun h e he => h ⟨e, he⟩⟩


end FK
end StatMech
