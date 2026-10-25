/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWFourier
import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit.Part2


namespace StatMech.Onsager

noncomputable def ons_turnRoot : ℂ := Complex.exp (Complex.I * (Real.pi / 4))

noncomputable def ons_spaceRoot (L : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / L)

end StatMech.Onsager
