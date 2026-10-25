/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.Foundations.StrassenFull.Part4
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


theorem mass_nonneg (μ : Measure (ConfigSpace E)) (ω : ConfigSpace E) :
    0 ≤ mass μ ω := ENNReal.toReal_nonneg


theorem measureReal_finset_eq_sum_mass (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (A : Finset (ConfigSpace E)) :
    μ.real (A : Set (ConfigSpace E)) = ∑ ω ∈ A, mass μ ω := by
  simp only [mass, measureReal_def]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  congr 1
  rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
        (fun ω _ => measurableSet_singleton ω)]
  congr 1; ext ω; simp


theorem sum_mass_eq_one (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] :
    ∑ ω : ConfigSpace E, mass μ ω = 1 := by
  simp only [mass]
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  rw [show (∑ ω : ConfigSpace E, μ {ω}) = μ Set.univ by
    rw [← measure_biUnion_finset (fun x _ y _ hxy => Set.disjoint_singleton.2 hxy)
          (fun ω _ => measurableSet_singleton ω)]
    congr 1; ext ω; simp]
  simp


theorem measure_singleton_eq_ofReal_mass (μ : Measure (ConfigSpace E))
    [IsFiniteMeasure μ] (ω : ConfigSpace E) : μ {ω} = ENNReal.ofReal (mass μ ω) := by
  rw [mass, ENNReal.ofReal_toReal (measure_ne_top μ _)]


theorem mass_down_dom (μ ν : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hdom : μ ≼ ν)
    (D : Finset (ConfigSpace E)) (hD : Transport.IsDown D) :
    ∑ ω ∈ D, mass ν ω ≤ ∑ ω ∈ D, mass μ ω := by
  have hDc_inc : IsIncreasing ((↑D)ᶜ : Set (ConfigSpace E)) := by
    apply IsLowerSet.compl
    intro a b hab hb
    simp only [Finset.mem_coe] at *
    exact hD b a hab hb
  have hmeas : MeasurableSet ((↑D)ᶜ : Set (ConfigSpace E)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  have hle := hdom _ hmeas hDc_inc
  have hsplit : ∀ (ρ : Measure (ConfigSpace E)) [IsProbabilityMeasure ρ],
      ρ.real ((↑D)ᶜ : Set (ConfigSpace E)) = 1 - ∑ ω ∈ D, mass ρ ω := by
    intro ρ _
    have h1 := probReal_add_probReal_compl (μ := ρ) (s := (↑D : Set (ConfigSpace E)))
        (DiscreteMeasurableSpace.forall_measurableSet _)
    rw [measureReal_finset_eq_sum_mass ρ D] at h1
    linarith
  rw [hsplit μ, hsplit ν] at hle
  linarith


end ConfigSpace
end StatMech
