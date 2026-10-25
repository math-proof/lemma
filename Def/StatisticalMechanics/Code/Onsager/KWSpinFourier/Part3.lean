/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part2


namespace StatMech.Onsager

noncomputable def ons_spinPhase (L : ℕ) (a : Fin 2) : ℂ :=
  Complex.exp (Complex.I * ((Real.pi * a.val / L : ℝ) : ℂ))

end StatMech.Onsager
