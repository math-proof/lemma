/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/AugmentedTurnCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.AugmentedTurnCancellation.Part3


namespace StatMech.Onsager

open BigOperators

def ons_involutiveLoopRev
    {E : Type*} {n : ℕ} [NeZero n]
    (rev : E → E) (loop : Fin n → E) : Fin n → E :=
  fun k ↦ rev (loop (-k))

end StatMech.Onsager
