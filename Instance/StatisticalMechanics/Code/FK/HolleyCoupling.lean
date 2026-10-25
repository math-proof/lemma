/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling
open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


instance (μ : ConfigSpace E → ℝ) : IsFiniteMeasure (measOfMass μ) := by
  classical
  refine ⟨?_⟩
  rw [measOfMass_apply]
  simp only [Set.mem_univ, if_true]
  exact ENNReal.sum_lt_top.2 (fun ω _ => ENNReal.ofReal_lt_top)


end FK
end StatMech
