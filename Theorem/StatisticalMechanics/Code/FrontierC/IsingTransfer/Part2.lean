/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DetLoopExpansion
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Order.Filter.AtTopBot.Basic
import Def.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part2
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

@[simp] lemma transferSpin_zero : transferSpin 0 = 1 := by simp [transferSpin]

@[simp] lemma transferSpin_one : transferSpin 1 = -1 := by simp [transferSpin]


end StatMech.FrontierC
