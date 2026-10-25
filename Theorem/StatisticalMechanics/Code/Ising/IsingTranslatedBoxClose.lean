/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingTranslatedBoxClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingCrossBoxCap.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem itb_plus_multiOpen_full_tendsto {β : ℝ} (hβ : 0 ≤ β) {h : ℝ} (hh : 0 ≤ h)
    (T : Finset (Site d)) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
    Tendsto (fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T))) := by
  set a : ℕ → ℝ := fun m => (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real
      (fmu_multiOpen (E := Site d) T) with ha
  have hanti : Antitone a := fun p q hpq => iti_plus_multiOpen_antitone hβ hh T hpq
  have hbdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨m, rfl⟩; exact measureReal_nonneg⟩
  have hfull : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf hanti hbdd
  have hsub : Tendsto (a ∘ φ) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T))) := iti_plus_multiOpen_tendsto β h φ T hconv
  have hsub2 : Tendsto (a ∘ φ) atTop (𝓝 (⨅ n, a n)) := hfull.comp hφ.tendsto_atTop
  rw [tendsto_nhds_unique hsub hsub2]; exact hfull


end Ising
end StatMech
