/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Def.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_windingSideCounterexample_dual_success_via_retainedContour :
    rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈
      rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  exact
    rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour
      rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_retainedFailureAnchoredContour

end Universality
end StatMech
