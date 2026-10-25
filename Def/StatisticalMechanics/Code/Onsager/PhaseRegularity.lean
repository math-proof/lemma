/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3


namespace StatMech.Onsager

noncomputable def ons_gIntBetaDeriv (beta k1 k2 : ℝ) : ℝ :=
  2 * Real.cosh (2 * beta) *
    (2 * Real.sinh (2 * beta) - Real.cos k1 - Real.cos k2)


noncomputable def ons_gIntBetaDeriv2 (beta k1 k2 : ℝ) : ℝ :=
  4 * Real.sinh (2 * beta) *
      (2 * Real.sinh (2 * beta) - Real.cos k1 - Real.cos k2) +
    8 * Real.cosh (2 * beta) ^ 2


noncomputable def ons_logGIntBetaDeriv (beta k1 k2 : ℝ) : ℝ :=
  ons_gIntBetaDeriv beta k1 k2 / ons_gInt beta k1 k2


noncomputable def ons_logGIntBetaDeriv2 (beta k1 k2 : ℝ) : ℝ :=
  (ons_gIntBetaDeriv2 beta k1 k2 * ons_gInt beta k1 k2 -
      ons_gIntBetaDeriv beta k1 k2 ^ 2) /
    ons_gInt beta k1 k2 ^ 2

end StatMech.Onsager
