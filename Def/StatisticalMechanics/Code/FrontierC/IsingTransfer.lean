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
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

noncomputable def isingTransferReal (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (beta + h), Real.exp (-beta);
     Real.exp (-beta), Real.exp (beta - h)]


noncomputable def isingTransfer (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (isingTransferReal beta h).map (algebraMap ℝ ℂ)

noncomputable def transferA (beta h : ℝ) : ℝ := Real.exp (beta + h)

noncomputable def transferB (beta : ℝ) : ℝ := Real.exp (-beta)

noncomputable def transferD (beta h : ℝ) : ℝ := Real.exp (beta - h)


noncomputable def isingTransferDisc (beta h : ℝ) : ℝ :=
  Real.sqrt ((transferA beta h - transferD beta h) ^ 2 +
    4 * transferB beta ^ 2)


noncomputable def isingTransferEigenPlus (beta h : ℝ) : ℝ :=
  (transferA beta h + transferD beta h + isingTransferDisc beta h) / 2


noncomputable def isingTransferEigenMinus (beta h : ℝ) : ℝ :=
  (transferA beta h + transferD beta h - isingTransferDisc beta h) / 2

end StatMech.FrontierC
