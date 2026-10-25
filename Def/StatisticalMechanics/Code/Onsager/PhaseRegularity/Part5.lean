/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part4


namespace StatMech.Onsager

noncomputable def ons_criticalParameterNeighborhood : Set ℝ :=
  {b | (1 / 2 : ℝ) < Real.sinh (2 * b) ∧ |Real.cosh (2 * b)| < 2}

end StatMech.Onsager
