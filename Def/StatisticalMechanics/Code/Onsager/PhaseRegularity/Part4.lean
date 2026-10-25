/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part3


namespace StatMech.Onsager

noncomputable def ons_noncriticalGap (beta : ℝ) : ℝ :=
  |Real.sinh (2 * beta) - 1|

noncomputable def ons_noncriticalNeighborhood (beta : ℝ) : Set ℝ :=
  {b | 0 < b ∧
    ons_noncriticalGap beta / 2 < |Real.sinh (2 * b) - 1| ∧
    |Real.cosh (2 * b)| < |Real.cosh (2 * beta)| + 1 ∧
    |Real.sinh (2 * b)| < |Real.sinh (2 * beta)| + 1}

end StatMech.Onsager
