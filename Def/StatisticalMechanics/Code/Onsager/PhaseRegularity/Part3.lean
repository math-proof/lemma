/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part2


namespace StatMech.Onsager

noncomputable def ons_criticalSecondKernelClamp (epsilon x y : ℝ) : ℝ :=
  -4 + 16 * ons_criticalKernelClamp epsilon x y

end StatMech.Onsager
