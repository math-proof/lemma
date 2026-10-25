/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch
open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS.BetaCMatch

open StatMech.OSSS.IntegrationSubcritical

open StatMech.OSSS.BetaThresholdBound


def bcm_subcriticalSet (θ : ℝ → ℝ) : Set ℝ := {β | θ β = 0}


end OSSS.BetaCMatch
end StatMech
