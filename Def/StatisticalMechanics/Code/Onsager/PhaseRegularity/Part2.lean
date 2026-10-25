/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity


namespace StatMech.Onsager

noncomputable def ons_criticalKernelClamp (epsilon x y : ℝ) : ℝ :=
  1 / max (2 - Real.cos x - Real.cos y) (1 - Real.cos epsilon)

end StatMech.Onsager
