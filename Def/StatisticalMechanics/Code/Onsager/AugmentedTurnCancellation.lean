/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_reversibleTurnMatrix
    {E : Type*} (dir : E → Fin 4) (omega : ℂ)
    (q : E → E → ℂ) : Matrix E E ℂ :=
  fun x y ↦ q x y * ons_turnW omega (dir y) (dir x)

end StatMech.Onsager
