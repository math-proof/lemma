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
import Theorem.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part2
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

noncomputable def isingRingExponent {n : ℕ} [NeZero n]
    (beta h : ℝ) (s : Fin n → Fin 2) : ℝ :=
  (∑ k : Fin n, beta * transferSpin (s k) * transferSpin (s (k + 1))) +
    h * ∑ k : Fin n, transferSpin (s k)


noncomputable def isingRingZ (n : ℕ) [NeZero n] (beta h : ℝ) : ℝ :=
  ∑ s : Fin n → Fin 2, Real.exp (isingRingExponent beta h s)

end StatMech.FrontierC
