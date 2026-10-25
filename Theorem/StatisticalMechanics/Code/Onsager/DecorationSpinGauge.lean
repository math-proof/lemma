/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2


namespace StatMech.Onsager

open BigOperators

@[simp] theorem ons_dirPhase_one_one (mu : Fin 4) :
    ons_dirPhase 1 1 mu = 1 := by
  fin_cases mu <;> simp [ons_dirPhase]

end StatMech.Onsager
