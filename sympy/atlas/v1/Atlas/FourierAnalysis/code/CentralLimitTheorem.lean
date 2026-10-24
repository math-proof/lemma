/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/CentralLimitTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace CentralLimitTheorem

open Complex Finset

noncomputable def expTaylorRemainder (x : ℝ) : ℂ :=
  cexp (↑x * I) - 1 - ↑x * I - (↑x * I) ^ 2 / 2
