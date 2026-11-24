module
public import Theorem.StatisticalMechanics.Code.Inequalities.Russo
public import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
public import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
public import Theorem.StatisticalMechanics.Code.Sharpness.ABFieldDeriv.Part2
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def qField (h : ℝ) : ℝ := 1 - Real.exp (-h)


end Sharpness
end StatMech
