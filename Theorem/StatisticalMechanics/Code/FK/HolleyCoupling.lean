/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Def.StatisticalMechanics.Code.FK.HolleyCoupling
open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


open scoped Classical in


theorem measOfMass_apply (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) :
    measOfMass μ A
      = ∑ ω : ConfigSpace E, if ω ∈ A then ENNReal.ofReal (μ ω) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold measOfMass
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hω : ω ∈ A <;> simp [hω]

end FK
end StatMech
