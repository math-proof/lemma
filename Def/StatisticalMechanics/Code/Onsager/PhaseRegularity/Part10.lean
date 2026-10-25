/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part9


namespace StatMech.Onsager

noncomputable def ons_complexNoncriticalDeviation (beta : ℝ) (z : ℂ) : ℝ :=
  ‖Complex.cosh (2 * z) ^ 2 - (Real.cosh (2 * beta) : ℂ) ^ 2‖ +
    2 * ‖Complex.sinh (2 * z) - (Real.sinh (2 * beta) : ℂ)‖

noncomputable def ons_complexNoncriticalNeighborhood (beta : ℝ) : Set ℂ :=
  {z | ons_complexNoncriticalDeviation beta z < ons_noncriticalGap beta ^ 2 / 2 ∧
    ‖Complex.cosh (2 * z)‖ < |Real.cosh (2 * beta)| + 1 ∧
    ‖Complex.sinh (2 * z)‖ < |Real.sinh (2 * beta)| + 1}

end StatMech.Onsager
