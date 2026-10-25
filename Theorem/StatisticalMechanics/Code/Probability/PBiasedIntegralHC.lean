/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedIntegralHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
import Def.StatisticalMechanics.Code.Probability.PBiasedIntegralHC
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

theorem pih_g_eq (p q z : ℝ) : pbt_g p q z = (pih_m p z) ^ 2 + pih_V p q z := by
  unfold pbt_g pih_m pih_V; ring


end StatMech.Probability
