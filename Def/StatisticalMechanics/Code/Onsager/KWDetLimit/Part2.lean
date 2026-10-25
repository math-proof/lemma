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
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit


namespace StatMech.Onsager

noncomputable def ons_spinDet (L : ℕ) (β : ℝ) (a b : Fin 2) : ℝ :=
  ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L,
    ons_symbolDispersion β
      (2 * Real.pi * (i + (a.val : ℝ) / 2) / L)
      (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)

end StatMech.Onsager
