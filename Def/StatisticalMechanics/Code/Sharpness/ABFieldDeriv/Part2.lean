/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Theorem.StatisticalMechanics.Code.Sharpness.ABFieldDeriv
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def paramOn (s : Finset E) (c : ℝ) (p : E → ℝ) : E → ℝ :=
  fun e => if e ∈ s then c else p e


end Sharpness
end StatMech
