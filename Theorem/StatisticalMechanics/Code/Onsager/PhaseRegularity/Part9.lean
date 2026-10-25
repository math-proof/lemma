/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part9


namespace StatMech.Onsager

theorem ons_gIntComplex_ofReal (beta k1 k2 : ℝ) :
    ons_gIntComplex (beta : ℂ) k1 k2 = (ons_gInt beta k1 k2 : ℂ) := by
  have harg : (2 : ℂ) * (beta : ℂ) = ((2 * beta : ℝ) : ℂ) := by norm_num
  unfold ons_gIntComplex ons_gInt
  rw [harg, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  push_cast
  rfl

end StatMech.Onsager
