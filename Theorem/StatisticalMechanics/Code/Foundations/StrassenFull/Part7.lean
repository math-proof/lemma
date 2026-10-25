/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Instance.StatisticalMechanics.Code.Foundations.StrassenFull.Part3
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


theorem exists_monotoneCoupling_of_stochasticallyDominated
    (μ ν : Measure (ConfigSpace E)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hdom : μ ≼ ν) :
    ∃ κ : Measure (ConfigSpace E × ConfigSpace E),
      IsFiniteMeasure κ ∧ MonotoneCoupling μ ν κ := by
  classical
  
  obtain ⟨c, hcpos, hrow, hcol⟩ :=
    Transport.exists_coupling_vec (P := ConfigSpace E) (mass μ) (mass ν)
      (mass_nonneg μ) (mass_nonneg ν)
      (by rw [sum_mass_eq_one μ, sum_mass_eq_one ν])
      (fun D hD => mass_down_dom μ ν hdom D hD)
  
  refine ⟨kappaOfVec c, inferInstance, ?_, ?_, ?_⟩
  · 
    apply Measure.ext_of_singleton
    intro ω
    rw [Measure.fst_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass μ ω, ← hrow ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).1 = ω
    · rw [if_pos (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.fst ⁻¹' {ω} from hq),
        if_pos hq]
    · rw [if_neg (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.fst ⁻¹' {ω} from hq),
        if_neg hq, ENNReal.ofReal_zero]
  · 
    apply Measure.ext_of_singleton
    intro ω
    rw [Measure.snd_apply (measurableSet_singleton ω), kappaOfVec_apply,
      measure_singleton_eq_ofReal_mass ν ω, ← hcol ω,
      ENNReal.ofReal_sum_of_nonneg (fun q _ => by split_ifs <;> [exact hcpos q; exact le_refl 0])]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : (q : ConfigSpace E × ConfigSpace E).2 = ω
    · rw [if_pos (show (q : ConfigSpace E × ConfigSpace E) ∈ Prod.snd ⁻¹' {ω} from hq),
        if_pos hq]
    · rw [if_neg (show (q : ConfigSpace E × ConfigSpace E) ∉ Prod.snd ⁻¹' {ω} from hq),
        if_neg hq, ENNReal.ofReal_zero]
  · 
    rw [kappaOfVec_apply]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    intro hmem
    
    exact hmem q.2

end ConfigSpace
end StatMech
