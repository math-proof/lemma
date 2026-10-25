/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
open MeasureTheory Finset

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def measOfMass (μ : ConfigSpace E → ℝ) : Measure (ConfigSpace E) :=
  ∑ ω : ConfigSpace E, (ENNReal.ofReal (μ ω)) • Measure.dirac ω

end FK
end StatMech
