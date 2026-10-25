/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalIntegrability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalTransfer.Part2
open scoped Real
open MeasureTheory Interval


namespace StatMech.Onsager

theorem ons_gInt_decompose (beta k1 k2 : ℝ) :
    ons_gInt beta k1 k2 =
      (Real.sinh (2 * beta) - 1) ^ 2 +
        Real.sinh (2 * beta) * (2 - Real.cos k1 - Real.cos k2) := by
  unfold ons_gInt
  have h := Real.cosh_sq_sub_sinh_sq (2 * beta)
  nlinarith

theorem ons_gInt_betaC (k1 k2 : ℝ) :
    ons_gInt ons_betaC k1 k2 = 2 - Real.cos k1 - Real.cos k2 := by
  rw [ons_gInt_decompose, ons_betaC_sinh]
  ring

end StatMech.Onsager
