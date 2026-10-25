/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part6
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

section ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]

open ConfigSpace Transport


instance (c : {p : ConfigSpace E × ConfigSpace E // p.1 ≤ p.2} → ℝ) :
    IsFiniteMeasure (kappaOfVec c) := by
  refine ⟨?_⟩
  rw [kappaOfVec_apply]
  simp only [Set.mem_univ, if_true]
  exact ENNReal.sum_lt_top.2 (fun q _ => ENNReal.ofReal_lt_top)


end ConfigSpace
end StatMech
