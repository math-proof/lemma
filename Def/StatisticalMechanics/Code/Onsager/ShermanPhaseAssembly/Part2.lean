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
import Theorem.StatisticalMechanics.Code.Onsager.ShermanPhaseAssembly


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_spinWalkRoot
    (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2) : ℂ :=
  ons_detWalkRoot (ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b))

end StatMech.Onsager
