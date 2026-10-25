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
import Theorem.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part4
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

noncomputable def isingTransferCorrelationRatio (beta h : ℝ) : ℝ :=
  isingTransferEigenMinus beta h / isingTransferEigenPlus beta h

end StatMech.FrontierC
