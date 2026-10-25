/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.Foundations.StrassenFull.Part5
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


open scoped Classical in
theorem kappaOfVec_apply
    (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ)
    (A : Set (ConfigSpace E × ConfigSpace E)) :
    kappaOfVec c A
      = ∑ q : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2},
          if (q : ConfigSpace E × ConfigSpace E) ∈ A then ENNReal.ofReal (c q) else 0 := by
  have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  unfold kappaOfVec
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  by_cases hq : (q : ConfigSpace E × ConfigSpace E) ∈ A <;> simp [hq]

end ConfigSpace
end StatMech
