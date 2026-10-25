/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


theorem boundaryGhostComparison
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    I.onePointPayment I.boundaryPairPayment I.emptyComparison

set_option linter.style.longLine false in


theorem simonFreeSum
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    I.boundaryGhostComparison

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
