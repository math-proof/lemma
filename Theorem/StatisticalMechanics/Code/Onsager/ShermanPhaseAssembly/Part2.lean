/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanPhaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLemma5
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Def.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly.Part2


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_spinWalkRoot_sq
    (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (a b : Fin 2) :
    ons_spinWalkRoot L x a b ^ 2 =
      (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  exact ons_detWalkRoot_sq _
    (ons_KWmatPhase_spectral_Sherman_small L hx a b)

end StatMech.Onsager
